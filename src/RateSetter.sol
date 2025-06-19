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
    function ilks(bytes32 ilk) external view returns (uint256 duty, uint256 rho);
    function file(bytes32 ilk, bytes32 what, uint256 data) external;
    function drip(bytes32 ilk) external;
}

interface YUSDSLike {
    function ilk() external view returns (bytes32);
    function syr() external view returns (uint256);
    function file(bytes32 what, uint256 data) external;
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
    uint256 public constant RAD = 10 ** 45;

    // --- Immutables ---
    JugLike   public immutable jug;
    YUSDSLike public immutable yusds;
    ConvLike  public immutable conv;
    bytes32   public immutable ilk;

    // --- Storage Variables ---
    mapping(address => uint256) public wards;
    mapping(address => uint256) public buds;
    Cfg     public syrCfg;
    Cfg     public dutyCfg;
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
        jug   = JugLike(_jug);
        yusds = YUSDSLike(_yusds);
        conv  = ConvLike(_conv);
        ilk   = yusds.ilk();

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
            require(data == 0 || data > RAD, "RateSetter/maxLine-insane-value");
            maxLine = data;
        } else if (what == "maxCap") {
            require(data < RAD, "RateSetter/maxCap-insane-value");
            maxCap = data;
        } else revert("RateSetter/file-unrecognized-param");
        emit File(what, data);
    }

    function file(bytes32 id, bytes32 what, uint256 data) external auth {
        Cfg storage cfg;
        if      (id == "SYR") cfg = syrCfg;
        else if (id == ilk)   cfg = dutyCfg;
        else revert("RateSetter/file-unrecognized-id");

        require(data <= type(uint16).max, "RateSetter/invalid-value");
        if (what == "min") {
            require(data <= cfg.max, "RateSetter/min-too-high");
            cfg.min = uint16(data);
        } else if (what == "max") {
            require(data >= cfg.min, "RateSetter/max-too-low");
            cfg.max = uint16(data);
        } else if (what == "step") {
            cfg.step = uint16(data);
        } else revert("RateSetter/file-unrecognized-param");
        emit File(id, what, data);
    }

    function _calcRate(uint256 bps, uint256 oldBps, Cfg memory cfg) internal view returns (uint256 ray) {
        require(cfg.step > 0,   "RateSetter/rate-not-configured");
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
        ray = conv.btor(bps);
        require(ray >= RAY, "RateSetter/invalid-rate-conv");
    }

    // Notes:
    // - It is intended to rewrite the same values, emit the event, and reset the toc count, even if there is no change.
    function set(uint256 syrBps, uint256 dutyBps, uint256 line, uint256 cap) external toll good {
        require(block.timestamp >= tau + toc, "RateSetter/too-early");
        toc = uint128(block.timestamp);

        uint256 ray = _calcRate({
            bps    : syrBps,
            oldBps : conv.rtob(yusds.syr()),
            cfg    : syrCfg
        });
        yusds.drip();
        yusds.file("syr", ray);

        (uint256 duty,) = jug.ilks(ilk);
        ray = _calcRate({
            bps    : dutyBps,
            oldBps : conv.rtob(duty),
            cfg    : dutyCfg
        });
        jug.drip(ilk);
        jug.file(ilk, "duty", ray);

        require(line <= maxLine, "RateSetter/line-too-high");
        yusds.file("line", line);

        require(cap <= maxCap, "RateSetter/cap-too-high");
        yusds.file("cap", cap);

        emit Set(syrBps, dutyBps, line, cap);
    }
}
