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

interface AuthorityLike {
    function canCall(address src, address dst, bytes4 sig) external view returns (bool);
}

interface YUsdsLike {
    function file(bytes32 what, uint256 data) external;
}

interface RateSetterLike {
    function file(bytes32 what, uint256 data) external;
}

contract YUsdsMom {
    // --- Storage ---
    address public owner;
    address public authority;

    // --- Immutables ---
    YUsdsLike immutable public yusds;

    // --- Events ---
    event SetOwner(address indexed owner);
    event SetAuthority(address indexed authority);
    event HaltRateSetter(address indexed rateSetter);
    event ZeroCap(address indexed rateSetter);
    event ZeroLine(address indexed rateSetter);

    // --- Modifiers ---
    modifier onlyOwner() {
        require(msg.sender == owner, "YUsdsMom/not-owner");
        _;
    }

    modifier auth() {
        require(isAuthorized(msg.sender, msg.sig), "YUsdsMom/not-authorized");
        _;
    }

    constructor(address yusds_) {
        yusds = YUsdsLike(yusds_);

        owner = msg.sender;
        emit SetOwner(msg.sender);
    }

    // --- Administration ---
    function setOwner(address owner_) external onlyOwner {
        owner = owner_;
        emit SetOwner(owner_);
    }

    function setAuthority(address authority_) external onlyOwner {
        authority = authority_;
        emit SetAuthority(authority_);
    }

    // --- Internal Functions ---
    function isAuthorized(address src, bytes4 sig) internal view returns (bool) {
        if (src == owner || src == address(this)) {
            return true;
        } else if (authority != address(0)) {
            return AuthorityLike(authority).canCall(src, address(this), sig);
        } else {
            return false;
        }
    }

    // --- Emergency Actions ---
    function haltRateSetter(address rateSetter) external auth {
        RateSetterLike(rateSetter).file("bad", 1);
        emit HaltRateSetter(rateSetter);
    }

    function zeroCap(address rateSetter) external auth {
        yusds.file("cap", 0);
        RateSetterLike(rateSetter).file("maxCap", 0);
        emit ZeroCap(rateSetter);
    }

    // Consider calling with line-mom to stop borrowing immediately
    function zeroLine(address rateSetter) external auth {
        yusds.file("line", 0);
        RateSetterLike(rateSetter).file("maxLine", 0);
        emit ZeroLine(rateSetter);
    }
}
