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
import { ClipMock } from "test/mocks/ClipMock.sol";

interface ConvLike {
    function btor(uint256) external pure returns (uint256);
    function rtob(uint256) external pure returns (uint256);
}

interface YUSDSLike {
    function wards(address) external view returns (uint256);
    function ysr() external view returns (uint256);
}

interface SPBEAMLike {
    function conv() external view returns (address);
}

contract MockBrokenConv {
    ConvLike immutable internal conv;

    constructor(address _conv) {
        conv = ConvLike(_conv);
    }

    function btor(uint256 /* bps */ ) public pure returns (uint256) {
        return 0;
    }

    function rtob(uint256 ray) public view returns (uint256) {
        return conv.rtob(ray);
    }
}

contract YUsdsRateSetterTest is DssTest {
    address constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    DssInstance     dss;
    YUsdsRateSetter rateSetter;
    ConvLike        conv;
    YUsds           yusds;
    address         pauseProxy;

    address bud = address(0xb0d);
    address bud2 = address(0xb0d2);

    bytes32 constant YSR = "YSR";
    bytes32 constant ILK = "LSEV2-SKY-A";

    event Kiss(address indexed usr);
    event Diss(address indexed usr);
    event File(bytes32 indexed id, bytes32 indexed what, uint256 data);
    event Set(bytes32 indexed id, uint256 bps);
    event Set(uint256 ysrBps, uint256 dutyBps, uint256 line, uint256 cap);

    function setUp() public {
        vm.createSelectFork(vm.envString("ETH_RPC_URL"));
        dss = MCD.loadFromChainlog(CHAINLOG);
        pauseProxy = dss.chainlog.getAddress("MCD_PAUSE_PROXY");

        YUsdsInstance memory inst = YUsdsDeploy.deploy(address(this), pauseProxy, address(new ClipMock(ILK)));
        yusds = YUsds(inst.yUsds);
        rateSetter = YUsdsRateSetter(inst.rateSetter);
        conv = ConvLike(address(rateSetter.conv()));

        address[] memory buds = new address[](2);
        buds[0] = bud;
        buds[1] = bud2;

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
            minDutyBps  : 2,
            maxDutyBps  : 4000,
            stepDutyBps : 200,
            buds        : buds
        });
        vm.startPrank(pauseProxy);
        YUsdsInit.init(dss, inst, conf);
        vm.stopPrank();
    }

    function _ysrBps() internal view returns (uint256 ysrBps) {
        ysrBps = conv.rtob(yusds.ysr());
    }

    function _duty() internal view returns (uint256 duty){
        (duty, ) = dss.jug.ilks(ILK);
    }

    function _dutyBps() internal view returns (uint256 dutyBps) {
        dutyBps = conv.rtob(_duty());
    }

    function _currentBps() internal view returns (uint256 ysrBps, uint256 dutyBps) {
        ysrBps  = _ysrBps();
        dutyBps = _dutyBps();
    }

    function testDeploy() public view {
        // Rate setter part only
        assertEq(address(rateSetter.jug()), address(dss.jug));
        assertEq(address(rateSetter.yusds()), address(yusds));
        assertEq(address(rateSetter.conv()), address(conv));
        assertEq(rateSetter.ilk(), ILK);
        assertEq(rateSetter.wards(address(this)), 0);
        assertEq(rateSetter.wards(pauseProxy), 1);
    }

    function testInit() public view {
        // Rate setter part only
        assertEq(dss.jug.wards(address(rateSetter)), 1);
        assertEq(yusds.wards(address(rateSetter)), 1);
        assertEq(rateSetter.tau(), 1 hours);
        assertEq(rateSetter.maxLine(), 1e9 * RAD);
        assertEq(rateSetter.maxCap(), 1e9 * WAD);
        (uint16 minYsr, uint16 maxYsr, uint256 ysrStep) = rateSetter.ysrCfg();
        assertEq(minYsr, 1);
        assertEq(maxYsr, 3000);
        assertEq(ysrStep, 100);
        (uint16 minDuty, uint16 maxDuty, uint256 dutyStep) = rateSetter.dutyCfg();
        assertEq(minDuty, 2);
        assertEq(maxDuty, 4000);
        assertEq(dutyStep, 200);
        assertEq(rateSetter.buds(bud), 1);
        assertEq(rateSetter.buds(bud2), 1);
        assertEq(dss.chainlog.getAddress("YUSDS_RATE_SETTER"), address(rateSetter));
    }

    function testConstructor() public {
        vm.expectEmit(true, true, true, true);
        emit Rely(address(this));
        YUsdsRateSetter rateSetter2 = new YUsdsRateSetter(
            dss.chainlog.getAddress("YUSDS"),
            SPBEAMLike(dss.chainlog.getAddress("MCD_SPBEAM")).conv()
        );

        assertEq(address(rateSetter2.yusds()), address(yusds));
        assertEq(address(rateSetter2.conv()), address(conv));
        assertEq(address(rateSetter2.jug()), address(dss.jug));
        assertEq(rateSetter2.ilk(), ILK);
        assertEq(rateSetter2.wards(address(this)), 1);
    }

    function testAuth() public {
        checkAuth(address(rateSetter), "YUsdsRateSetter");
    }

    function testAuthMethods() public {
        checkModifier(address(rateSetter), "YUsdsRateSetter/not-authorized", [YUsdsRateSetter.kiss.selector, YUsdsRateSetter.diss.selector]);
    }

    function testTollMethods() public {
        checkModifier(address(rateSetter), "YUsdsRateSetter/not-facilitator", [YUsdsRateSetter.set.selector]);
    }

    function testGoodMethods() public {
        vm.startPrank(pauseProxy);
        rateSetter.file("bad", 1);
        rateSetter.kiss(address(this));
        vm.stopPrank();

        checkModifier(address(rateSetter), "YUsdsRateSetter/module-halted", [YUsdsRateSetter.set.selector]);
    }

    function testKissDiss() public {
        address who = address(0x0ddaf);
        assertEq(rateSetter.buds(who), 0);

        vm.expectEmit(true, true, true, true);
        emit Kiss(who);
        vm.prank(pauseProxy); rateSetter.kiss(who);
        assertEq(rateSetter.buds(who), 1);

        vm.expectEmit(true, true, true, true);
        emit Diss(who);
        vm.prank(pauseProxy); rateSetter.diss(who);
        assertEq(rateSetter.buds(who), 0);
    }

    function testFile() public {
        checkFileUint(address(rateSetter), "YUsdsRateSetter", ["bad", "tau", "toc", "maxLine", "maxCap"]);

        vm.startPrank(pauseProxy);

        vm.expectRevert("YUsdsRateSetter/invalid-bad-value");
        rateSetter.file("bad", 2);

        vm.expectRevert("YUsdsRateSetter/invalid-tau-value");
        rateSetter.file("tau", uint256(type(uint64).max) + 1);

        vm.expectRevert("YUsdsRateSetter/invalid-toc-value");
        rateSetter.file("toc", uint256(type(uint128).max) + 1);

        vm.expectRevert("YUsdsRateSetter/maxLine-irrelevant-value");
        rateSetter.file("maxLine", RAD - 1);

        vm.expectRevert("YUsdsRateSetter/maxCap-insane-value");
        rateSetter.file("maxCap", RAD);

        vm.stopPrank();

        vm.expectRevert("YUsdsRateSetter/not-authorized");
        rateSetter.file("bad", 1);
    }

    function testFileYsr() public {
        (uint16 min, uint16 max, uint16 step) = rateSetter.ysrCfg();
        assertEq(min, 1);
        assertEq(max, 3000);
        assertEq(step, 100);

        vm.startPrank(pauseProxy);
        vm.expectEmit(true, true, true, true);
        emit File(YSR, "min", 100);
        rateSetter.file(YSR, "min", 100);
        vm.expectEmit(true, true, true, true);
        emit File(YSR, "max", 2000);
        rateSetter.file(YSR, "max", 2000);
        vm.expectEmit(true, true, true, true);
        emit File(YSR, "step", 420);
        rateSetter.file(YSR, "step", 420);
        vm.stopPrank();

        (min, max, step) = rateSetter.ysrCfg();
        assertEq(min, 100);
        assertEq(max, 2000);
        assertEq(step, 420);
    }

    function testFileIlk() public {
        (uint16 min, uint16 max, uint16 step) = rateSetter.dutyCfg();
        assertEq(min, 2);
        assertEq(max, 4000);
        assertEq(step, 200);

        vm.startPrank(pauseProxy);
        vm.expectEmit(true, true, true, true);
        emit File(ILK, "min", 100);
        rateSetter.file(ILK, "min", 100);
        vm.expectEmit(true, true, true, true);
        emit File(ILK, "max", 2000);
        rateSetter.file(ILK, "max", 2000);
        vm.expectEmit(true, true, true, true);
        emit File(ILK, "step", 420);
        rateSetter.file(ILK, "step", 420);
        vm.stopPrank();

        (min, max, step) = rateSetter.dutyCfg();
        assertEq(min, 100);
        assertEq(max, 2000);
        assertEq(step, 420);
    }

    function testRevertFileInvalid() public {
        vm.startPrank(pauseProxy);
        (uint16 min, uint16 max,) = rateSetter.dutyCfg();

        vm.expectRevert("YUsdsRateSetter/min-too-high");
        rateSetter.file(ILK, "min", max + 1);

        vm.expectRevert("YUsdsRateSetter/max-too-low");
        rateSetter.file(ILK, "max", min - 1);

        vm.expectRevert("YUsdsRateSetter/file-unrecognized-param");
        rateSetter.file(ILK, "unknown", 100);

        vm.expectRevert("YUsdsRateSetter/invalid-value");
        rateSetter.file(ILK, "max", uint256(type(uint16).max) + 1);

        vm.expectRevert("YUsdsRateSetter/file-unrecognized-id");
        rateSetter.file("MOG-A", "min", 100);

        vm.stopPrank();

        vm.expectRevert("YUsdsRateSetter/not-authorized");
        rateSetter.file(ILK, "min", 100);
    }

    function testSet() public {
        (uint256 ysrTarget, uint256 dutyTarget) = (_ysrBps() + 50, _dutyBps() + 50);

        vm.expectEmit(true, true, true, true);
        emit Set(ysrTarget, dutyTarget, 50_000_000 * RAD, 60_000_000 * WAD);
        vm.prank(bud); rateSetter.set(ysrTarget, dutyTarget, 50_000_000 * RAD, 60_000_000 * WAD);

        assertEq(yusds.ysr(), conv.btor(ysrTarget));
        assertEq(_duty(), conv.btor(dutyTarget));
        assertEq(yusds.line(), 50_000_000 * RAD);
        assertEq(yusds.cap(), 60_000_000 * WAD);
    }

    // following tests check that can still set rates,
    // even if previously the rates were outside of the range.
    function testSetRatesAboveMax() public {
        dss.jug.drip(ILK);
        vm.startPrank(pauseProxy);
        yusds.file("ysr", conv.btor(3050)); // outside range
        dss.jug.file(ILK, "duty", conv.btor(4050)); // outside range
        vm.stopPrank();

        vm.startPrank(bud);
        rateSetter.set(2999, 3999, 0, 0);
        vm.stopPrank();

        assertEq(yusds.ysr(), conv.btor(2999));
        assertEq(_duty(), conv.btor(3999));
    }

    function testSetRatesBelowMin() public {
        dss.jug.drip(ILK);
        vm.startPrank(pauseProxy);
        yusds.file("ysr", conv.btor(0)); // outside range
        dss.jug.file(ILK, "duty", conv.btor(0)); // outside range
        vm.stopPrank();

        vm.startPrank(bud);
        rateSetter.set(50, 50, 0, 0);
        vm.stopPrank();

        assertEq(yusds.ysr(), conv.btor(50));
        assertEq(_duty(), conv.btor(50));
    }

    function testRevertSetYsrNotConfiguredRate() public {
        vm.prank(pauseProxy); rateSetter.file(YSR, "step", 0);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/rate-not-configured");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 0, 0);
    }

    function testRevertSetDutyNotConfiguredRate() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "step", 0);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/rate-not-configured");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 0, 0);
    }

    function testRevertSetYsrBelowMin() public {
        vm.prank(pauseProxy); rateSetter.file(YSR, "min", 100);
        uint256 dutyBps = _dutyBps();
        vm.expectRevert("YUsdsRateSetter/below-min");
        vm.prank(bud); rateSetter.set(50, dutyBps, 0, 0);
    }

    function testRevertSetDutyBelowMin() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "min", 100);
        uint256 ysrBps = _ysrBps();
        vm.expectRevert("YUsdsRateSetter/below-min");
        vm.prank(bud); rateSetter.set(ysrBps, 50, 0, 0);
    }

    function testRevertSetYsrAboveMax() public {
        vm.prank(pauseProxy); rateSetter.file(YSR, "max", 100);
        uint256 dutyBps = _dutyBps();
        vm.expectRevert("YUsdsRateSetter/above-max");
        vm.prank(bud); rateSetter.set(150, dutyBps, 0, 0);
    }

    function testRevertSetDutyAboveMax() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "max", 100);
        uint256 ysrBps = _ysrBps();
        vm.expectRevert("YUsdsRateSetter/above-max");
        vm.prank(bud); rateSetter.set(ysrBps, 150, 0, 0);
    }

    function testRevertSetYsrDeltaAboveStep() public {
        vm.prank(pauseProxy); rateSetter.file(YSR, "step", 100);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/delta-above-step");
        vm.prank(bud); rateSetter.set(ysrBps + 101, dutyBps, 0, 0);
    }

    function testRevertSetDutyDeltaAboveStep() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "step", 100);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/delta-above-step");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps + 101, 0, 0);
    }

    function testRevertLineTooHigh() public {
        vm.prank(pauseProxy); rateSetter.file("maxLine", 100 * RAD);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/line-too-high");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 100 * RAD + 1, 0);
    }

    function testRevertCapTooHigh() public {
        vm.prank(pauseProxy); rateSetter.file("maxCap", 100 * WAD);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/cap-too-high");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 0, 100 * WAD + 1);
    }

    function testRevertSetBeforeCooldown() public {
        vm.prank(pauseProxy); rateSetter.file("tau", 100);
        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 0, 0);

        vm.warp(block.timestamp + 99);

        vm.expectRevert("YUsdsRateSetter/too-early");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 0, 0);
    }

    function testRevertSetMalfunctioningConv() public {
        // Clone the good conv code (before we break it below), so we can call conv.rtob() in MockBrokenConv
        vm.etch(address(0x123), address(conv).code);

        // Mutate the conv code that is used in rateSetter
        vm.etch(address(conv), address(new MockBrokenConv(address(0x123))).code);

        (uint256 ysrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("YUsdsRateSetter/invalid-rate-conv");
        vm.prank(bud); rateSetter.set(ysrBps, dutyBps, 0, 0);
    }
}
