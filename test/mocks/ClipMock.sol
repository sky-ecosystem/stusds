// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.21;

contract ClipMock {
    bytes32 public ilk;
    uint256 public Due;

    constructor(bytes32 ilk_) {
        ilk = ilk_;
    }

    function setDue(uint256 Due_) external {
        Due = Due_;
    }
}
