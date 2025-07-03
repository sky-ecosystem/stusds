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
    function jug() external view returns (address);
    function clip() external view returns (address);
    function vow() external view returns (address);
    function ilk() external view returns (bytes32);
    function file(bytes32, uint256) external;
    function drip() external returns (uint256);
    function rely(address) external;
}

interface AutoLineLike {
    function remIlk(bytes32) external;
}

interface RateSetterLike {
    function jug() external view returns (address);
    function yusds() external view returns (address);
    function conv() external view returns (address);
    function file(bytes32, uint256) external;
    function file(bytes32, bytes32, uint256) external;
    function kiss(address) external;
    function rely(address) external;
}

interface SPBEAMLike {
    function conv() external view returns (address);
}

interface YUsdsMomLike {
    function yusds() external view returns (address);
    function setAuthority(address) external;
}

struct YUsdsConfig {
    address clip;
    uint256 ysr;
    uint256 cap;
    uint256 line;

    // RateSetter configuration
    uint256   tau;
    uint256   maxLine;
    uint256   maxCap;
    uint256   minYsrBps;
    uint256   maxYsrBps;
    uint256   stepYsrBps;
    uint256   minDutyBps;
    uint256   maxDutyBps;
    uint256   stepDutyBps;
    address[] buds;
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

        require(YUsdsLike(instance.yUsds).usdsJoin() == dss.chainlog.getAddress("USDS_JOIN"), "YUsdsInit/usdsJoin-does-not-match");
        require(YUsdsLike(instance.yUsds).jug()      == address(dss.jug),                     "YUsdsInit/jug-does-not-match");
        require(YUsdsLike(instance.yUsds).clip()     == cfg.clip,                             "YUsdsInit/clip-does-not-match");
        require(YUsdsLike(instance.yUsds).vow()      == address(dss.vow),                     "YUsdsInit/vow-does-not-match");

        require(cfg.ysr >= RAY && cfg.ysr <= RATES_ONE_HUNDRED_PCT, "YUsdsInit/ysr-out-of-boundaries");

        require(RateSetterLike(instance.rateSetter).yusds() == instance.yUsds, "YUsdsInit/yusds-does-not-match");
        require(RateSetterLike(instance.rateSetter).conv()  == SPBEAMLike(dss.chainlog.getAddress("MCD_SPBEAM")).conv(), "YUsdsInit/conv-does-not-match");

        require(YUsdsMomLike(instance.mom).yusds() == instance.yUsds, "YUsdsInit/yusds-does-not-match");

        dss.vat.rely(instance.yUsds);

        bytes32 ilk = YUsdsLike(instance.yUsds).ilk();

        AutoLineLike(dss.chainlog.getAddress("MCD_IAM_AUTO_LINE")).remIlk(ilk);

        YUsdsLike(instance.yUsds).drip();
        YUsdsLike(instance.yUsds).file("ysr",  cfg.ysr);
        YUsdsLike(instance.yUsds).file("cap",  cfg.cap);
        YUsdsLike(instance.yUsds).file("line", cfg.line);

        // RateSetter Configuration
        dss.jug.rely(instance.rateSetter);
        YUsdsLike(instance.yUsds).rely(instance.rateSetter);

        RateSetterLike(instance.rateSetter).file("tau",     cfg.tau);
        RateSetterLike(instance.rateSetter).file("maxLine", cfg.maxLine);
        RateSetterLike(instance.rateSetter).file("maxCap",  cfg.maxCap);

        // Note: we configure max first on purpose to initially pass the max > min validation
        RateSetterLike(instance.rateSetter).file("YSR", "max",  cfg.maxYsrBps);
        RateSetterLike(instance.rateSetter).file("YSR", "min",  cfg.minYsrBps);
        RateSetterLike(instance.rateSetter).file("YSR", "step", cfg.stepYsrBps);

        RateSetterLike(instance.rateSetter).file(ilk, "max",  cfg.maxDutyBps);
        RateSetterLike(instance.rateSetter).file(ilk, "min",  cfg.minDutyBps);
        RateSetterLike(instance.rateSetter).file(ilk, "step", cfg.stepDutyBps);

        for (uint256 i; i < cfg.buds.length; i ++) {
            RateSetterLike(instance.rateSetter).kiss(cfg.buds[i]);
        }

        // Mom Configuration
        YUsdsLike(instance.yUsds).rely(instance.mom);
        RateSetterLike(instance.rateSetter).rely(instance.mom);
        YUsdsMomLike(instance.mom).setAuthority(dss.chainlog.getAddress("MCD_ADM"));

        dss.chainlog.setAddress("YUSDS",             instance.yUsds);
        dss.chainlog.setAddress("YUSDS_IMP",         instance.yUsdsImp);
        dss.chainlog.setAddress("YUSDS_RATE_SETTER", instance.rateSetter);
        dss.chainlog.setAddress("YUSDS_MOM",         instance.mom);
    }
}
