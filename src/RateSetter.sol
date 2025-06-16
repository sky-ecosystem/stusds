// SPDX-FileCopyrightText: 2025 Dai Foundation <www.daifoundation.org>
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

pragma solidity ^0.8.21;

interface JugLike {
    function file(bytes32 ilk, bytes32 what, uint256 data) external;
    function ilks(bytes32 ilk) external view returns (uint256 duty, uint256 rho);
    function drip(bytes32 ilk) external;
}

interface YUSDSLike {
    function ilk() external view returns (bytes32);
    function file(bytes32 what, uint256 data) external;
    function syr() external view returns (uint256);
    function drip() external;
}

interface ConvLike {
    function btor(uint256 bps) external pure returns (uint256 ray);
    function rtob(uint256 ray) external pure returns (uint256 bps);
}

contract RateSetter {

    // --- Structs ---
    // All values are in basis points (1 bp = 0.01%)
    struct Cfg {
        uint16 min;  // Minimum allowed rate
        uint16 max;  // Maximum allowed rate
        uint16 step; // Maximum allowed rate change per update
    }

    // --- Constants ---
    uint256 public constant RAY = 10 ** 27;

    // --- Immutables ---
    JugLike   public immutable jug;
    YUSDSLike public immutable yusds;
    ConvLike  public immutable conv;
    bytes32   public immutable engineIlk;

    // --- Storage Variables ---
    mapping(address => uint256) public wards;
    mapping(address => uint256) public buds;
    mapping(bytes32 => Cfg)     public cfgs;

    uint256 public maxLine; // [rad]
    uint256 public maxCap;  // [wad]
    
    uint8   public bad; // Circuit breaker flag
    uint64  public tau; // Cooldown period between rate changes in seconds
    uint128 public toc; // Last time when rates were updated (Unix timestamp)

    // --- Events ---
    event Rely(address indexed usr);
    event Deny(address indexed usr);
    event Kiss(address indexed usr);
    event Diss(address indexed usr);
    event File(bytes32 indexed what, uint256 data);
    event File(bytes32 indexed id, bytes32 indexed what, uint256 data);
    event Set(uint256 syrBps, uint256 dutyBps, uint256 line, uint256 cap);

    // --- Modifiers ---
    modifier auth() {
        require(wards[msg.sender] == 1, "RateSetter/not-authorized");
        _;
    }

    modifier toll() {
        require(buds[msg.sender] == 1, "RateSetter/not-facilitator");
        _;
    }

    modifier good() {
        require(bad == 0, "RateSetter/module-halted");
        _;
    }

    constructor(address _jug, address _yusds, address _conv) {
        jug = JugLike(_jug);
        yusds = YUSDSLike(_yusds);
        conv = ConvLike(_conv);
        engineIlk = yusds.ilk();

        wards[msg.sender] = 1;
        emit Rely(msg.sender);
    }

    // --- Administration ---
    function rely(address usr) external auth {
        wards[usr] = 1;
        emit Rely(usr);
    }

    function deny(address usr) external auth {
        wards[usr] = 0;
        emit Deny(usr);
    }

    function kiss(address usr) external auth {
        buds[usr] = 1;
        emit Kiss(usr);
    }

    function diss(address usr) external auth {
        buds[usr] = 0;
        emit Diss(usr);
    }

    function file(bytes32 what, uint256 data) external auth {
        if (what == "bad") {
            require(data == 0 || data == 1, "RateSetter/invalid-bad-value");
            bad = uint8(data);
        } else if (what == "tau") {
            require(data <= type(uint64).max, "RateSetter/invalid-tau-value");
            tau = uint64(data);
        } else if (what == "toc") {
            require(data <= type(uint128).max, "RateSetter/invalid-toc-value");
            toc = uint128(data);
        } else if (what == "maxLine") {
            require(data <= type(uint128).max, "RateSetter/invalid-maxLinec-value");
            maxLine = uint128(data); // TODO: further sanity checks?
        } else if (what == "maxCap") {
            require(data <= type(uint128).max, "RateSetter/invalid-maxCap-value");
            maxCap = uint128(data); // TODO: further sanity checks?
        } else revert("RateSetter/file-unrecognized-param");
        emit File(what, data);
    }

    function file(bytes32 id, bytes32 what, uint256 data) external auth {
        require(id == "SYR" || id == engineIlk, "RateSetter/invalid-id");
        require(data <= type(uint16).max, "RateSetter/invalid-value");
        if (what == "min") {
            require(data <= cfgs[id].max, "RateSetter/min-too-high");
            cfgs[id].min = uint16(data);
        } else if (what == "max") {
            require(data >= cfgs[id].min, "RateSetter/max-too-low");
            cfgs[id].max = uint16(data);
        } else if (what == "step") {
            cfgs[id].step = uint16(data);
        } else revert("RateSetter/file-unrecognized-param");
        emit File(id, what, data);
    }

    function _setRates(uint256 syrBps, uint256 dutyBps) internal {
        bytes32 id;
        uint256 bps;
        uint256 oldBps;

        for (uint256 i = 0; i < 2; i++) {
            if (i == 0) {
                (id, bps, oldBps) = ("SYR", syrBps, conv.rtob(yusds.syr()));
            } else {
                (id, bps) = (engineIlk, dutyBps);
                (uint256 duty,) = JugLike(jug).ilks(id);
                oldBps = conv.rtob(duty);
            }

            Cfg memory cfg = cfgs[id];

            require(cfg.step > 0, "RateSetter/rate-not-configured");
            require(bps >= cfg.min, "RateSetter/below-min");
            require(bps <= cfg.max, "RateSetter/above-max");

            if (oldBps < cfg.min) {
                oldBps = cfg.min;
            } else if (oldBps > cfg.max) {
                oldBps = cfg.max;
            }

            // Calculates absolute difference between the old and the new rate
            uint256 delta = bps > oldBps ? bps - oldBps : oldBps - bps;
            require(delta <= cfg.step, "RateSetter/delta-above-step");

            // Execute the update
            uint256 ray = conv.btor(bps);
            require(ray >= RAY, "RateSetter/invalid-rate-conv");
            if (id == "SYR") {
                yusds.drip();
                yusds.file("syr", ray);
            } else {
                jug.drip(id);
                jug.file(id, "duty", ray);
            }
        }
    }

    function _setCaps(uint256 line, uint256 cap) internal {
        require(line <= maxLine, "RateSetter/line-too-high");
        require(cap  <= maxCap, "RateSetter/cap-too-high");

        yusds.file("line", line);
        yusds.file("cap", cap);
    }

    function set(uint256 syrBps, uint256 dutyBps, uint256 line, uint256 cap) external toll good {
        require(block.timestamp >= tau + toc, "RateSetter/too-early");
        toc = uint128(block.timestamp);

        _setRates(syrBps, dutyBps);
        _setCaps(line, cap);

        emit Set(syrBps, dutyBps, line, cap);
    }
}
