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

import "dss-test/DssTest.sol";

import { YUsdsRateSetter } from "src/YUsdsRateSetter.sol";
import { YUsds } from "src/YUsds.sol";
import { YUsdsInstance } from "deploy/YUsdsInstance.sol";
import { YUsdsDeploy } from "deploy/YUsdsDeploy.sol";
import { YUsdsInit, YUsdsConfig } from "deploy/YUsdsInit.sol";
import { YUsdsMom } from "src/YUsdsMom.sol";
import { ClipMock } from "test/mocks/ClipMock.sol";

interface ChiefLike {
    function hat() external view returns (address);
}

contract YUsdsMomTest is DssTest {
    address constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    DssInstance     dss;
    ChiefLike       chief;
    YUsdsRateSetter rateSetter;
    YUsds           yusds;
    YUsdsMom        mom;
    address         pauseProxy;

    event SetOwner(address indexed owner);
    event SetAuthority(address indexed authority);
    event HaltRateSetter(address indexed rateSetter);
    event ZeroCap(address indexed rateSetter);
    event ZeroLine(address indexed rateSetter);

    function setUp() public {
        vm.createSelectFork(vm.envString("ETH_RPC_URL"), 22725635); // TODO: remove the specific block
        dss = MCD.loadFromChainlog(CHAINLOG);
        chief = ChiefLike(dss.chainlog.getAddress("MCD_ADM"));
        pauseProxy = dss.chainlog.getAddress("MCD_PAUSE_PROXY");

        YUsdsInstance memory inst = YUsdsDeploy.deploy(address(this), pauseProxy, address(new ClipMock("LSEV2-SKY-A")));
        yusds = YUsds(inst.yUsds);
        rateSetter = YUsdsRateSetter(inst.rateSetter);
        mom = YUsdsMom(inst.mom);

        YUsdsConfig memory conf = YUsdsConfig({
            clip        : address(yusds.clip()),
            ysr         : 1000000001547125957863212448,
            cap         : type(uint256).max,
            line        : type(uint256).max,
            tau         : 1 hours,
            maxLine     : 1e9 * RAD,
            maxCap      : 1e9 * WAD,
            minYsrBps   : 1,
            maxYsrBps   : 3000,
            stepYsrBps  : 100,
            minDutyBps  : 1,
            maxDutyBps  : 3000,
            stepDutyBps : 100,
            buds        : new address[](0)
        });
        vm.startPrank(pauseProxy);
        YUsdsInit.init(dss, inst, conf);
        vm.stopPrank();
    }

    function testDeploy() public view {
        // Mom part only
        assertEq(address(mom.yusds()), address(yusds));
        assertEq(mom.owner(), pauseProxy);
    }

    function testInit() public view {
        // Mom part only
        assertEq(yusds.wards(address(mom)), 1);
        assertEq(rateSetter.wards(address(mom)), 1);
        assertEq(mom.authority(), dss.chainlog.getAddress("MCD_ADM"));
        assertEq(dss.chainlog.getAddress("YUSDS_MOM"), address(mom));
    }

    function testConstructor() public {
        vm.expectEmit(true, true, true, true);
        emit SetOwner(address(this));
        YUsdsMom mom2 = new YUsdsMom(address(yusds));

        assertEq(address(mom2.yusds()), address(yusds));
        assertEq(mom2.owner(), address(this));
    }

    function testOnlyOwnerMethods() public {
        checkModifier(
            address(mom), "YUsdsMom/not-owner", [YUsdsMom.setOwner.selector, YUsdsMom.setAuthority.selector]
        );
    }

    function testAuthMethods() public {
        checkModifier(address(mom), "YUsdsMom/not-authorized", [YUsdsMom.haltRateSetter.selector, YUsdsMom.zeroCap.selector, YUsdsMom.zeroLine.selector]);

        vm.prank(address(pauseProxy));
        mom.setAuthority(address(0));
        checkModifier(address(mom), "YUsdsMom/not-authorized", [YUsdsMom.haltRateSetter.selector, YUsdsMom.zeroCap.selector, YUsdsMom.zeroLine.selector]);
    }

    function testSetOwner() public {
        vm.prank(address(pauseProxy));
        vm.expectEmit(true, true, true, true);
        emit SetOwner(address(0x1234));
        mom.setOwner(address(0x1234));
        assertEq(mom.owner(), address(0x1234));
    }

    function testSetAuthority() public {
        vm.prank(address(pauseProxy));
        vm.expectEmit(true, true, true, true);
        emit SetAuthority(address(0x123));
        mom.setAuthority(address(0x123));
        assertEq(address(mom.authority()), address(0x123));
    }

    function checkHalt(address who) internal {
        vm.prank(who);
        vm.expectEmit(true, true, true, true);
        emit HaltRateSetter(address(rateSetter));
        mom.haltRateSetter(address(rateSetter));
        assertEq(rateSetter.bad(), 1);
    }

    function testHaltOwner() public {
        checkHalt(address(pauseProxy));
    }

    function testHaltHat() public {
        checkHalt(chief.hat());
    }

    function checkZeroCap(address who) internal {
        vm.prank(who);
        vm.expectEmit(true, true, true, true);
        emit ZeroCap(address(rateSetter));
        mom.zeroCap(address(rateSetter));
        assertEq(yusds.cap(), 0);
        assertEq(rateSetter.maxCap(), 0);
    }

    function testZeroCapOwner() public {
        checkHalt(address(pauseProxy));
    }

    function testZeroCapHat() public {
        checkHalt(chief.hat());
    }

    function checkZeroLine(address who) internal {
        vm.prank(who);
        vm.expectEmit(true, true, true, true);
        emit ZeroLine(address(rateSetter));
        mom.zeroLine(address(rateSetter));
        assertEq(yusds.line(), 0);
        assertEq(rateSetter.maxLine(), 0);
    }

    function testZeroLineOwner() public {
        checkZeroLine(address(pauseProxy));
    }

    function testZeroLineHat() public {
        checkZeroLine(chief.hat());
    }
}
