// SPDX-FileCopyrightText: © 2023 Dai Foundation <www.daifoundation.org>
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

pragma solidity >=0.8.0;

import { DssInstance } from "dss-test/MCD.sol";
import { YUsdsInstance } from "./YUsdsInstance.sol";

interface YUsdsLike {
    function version() external view returns (string memory);
    function getImplementation() external view returns (address);
    function usdsJoin() external view returns (address);
    function vat() external view returns (address);
    function jug() external view returns (address);
    function clip() external view returns (address);
    function vow() external view returns (address);
    function file(bytes32, uint256) external;
    function drip() external returns (uint256);
}

interface UsdsJoinLike {
    function usds() external view returns (address);
}

struct YUsdsConfig {
    address clip;
    uint256 syr;
    uint256 sCap;
    uint256 bCap;
}

library YUsdsInit {

    uint256 constant internal RAY                   = 10**27;
    uint256 constant internal RATES_ONE_HUNDRED_PCT = 1000000021979553151239153027;

    function init(
        DssInstance   memory dss,
        YUsdsInstance memory instance,
        YUsdsConfig   memory cfg
    ) internal {
        require(keccak256(abi.encodePacked(YUsdsLike(instance.yUsds).version())) == keccak256(abi.encodePacked("1")), "YUsdsInit/version-does-not-match");
        require(YUsdsLike(instance.yUsds).getImplementation() == instance.yUsdsImp, "YUsdsInit/imp-does-not-match");

        require(YUsdsLike(instance.yUsds).vat()      == address(dss.vat),                     "YUsdsInit/vat-does-not-match");
        require(YUsdsLike(instance.yUsds).jug()      == address(dss.jug),                     "YUsdsInit/jug-does-not-match");
        require(YUsdsLike(instance.yUsds).usdsJoin() == dss.chainlog.getAddress("USDS_JOIN"), "YUsdsInit/usdsJoin-does-not-match");
        require(YUsdsLike(instance.yUsds).clip()     == cfg.clip,                             "YUsdsInit/usdsJoin-does-not-match");
        require(YUsdsLike(instance.yUsds).vow()      == address(dss.vow),                     "YUsdsInit/vow-does-not-match");

        require(cfg.syr >= RAY && cfg.syr <= RATES_ONE_HUNDRED_PCT, "YUsdsInit/syr-out-of-boundaries");

        dss.vat.rely(instance.yUsds);

        YUsdsLike(instance.yUsds).drip();
        YUsdsLike(instance.yUsds).file("syr", cfg.syr);
        YUsdsLike(instance.yUsds).file("sCap", cfg.sCap);
        YUsdsLike(instance.yUsds).file("bCap", cfg.bCap);

        dss.chainlog.setAddress("YUSDS",     instance.yUsds);
        dss.chainlog.setAddress("YUSDS_IMP", instance.yUsdsImp);
    }
}
