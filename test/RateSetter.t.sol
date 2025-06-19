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

import { RateSetter } from "src/RateSetter.sol";
import { YUsds } from "src/YUsds.sol";
import { YUsdsInstance } from "deploy/YUsdsInstance.sol";
import { YUsdsDeploy } from "deploy/YUsdsDeploy.sol";
import { YUsdsInit, YUsdsConfig } from "deploy/YUsdsInit.sol";
import { ClipMock } from "test/mocks/ClipMock.sol";

interface ConvLike {
    function btor(uint256 bps) external pure returns (uint256 ray);
    function rtob(uint256 ray) external pure returns (uint256 bps);
}

interface YUSDSLike {
    function wards(address usr) external view returns (uint256);
    function syr() external view returns (uint256);
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

contract RateSetterTest is DssTest {
    address constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    DssInstance dss;
    RateSetter  rateSetter;
    ConvLike    conv;
    YUsds       yusds;
    address     clip;
    address     pauseProxy;

    address bud = address(0xb0d);

    bytes32 constant ILK = "LSEV2-SKY-A";
    bytes32 constant SYR = "SYR";

    event Kiss(address indexed usr);
    event Diss(address indexed usr);
    event File(bytes32 indexed id, bytes32 indexed what, uint256 data);
    event Set(bytes32 indexed id, uint256 bps);
    event Set(uint256 syrBps, uint256 dutyBps, uint256 line, uint256 cap);

    function setUp() public {
        vm.createSelectFork(vm.envString("ETH_RPC_URL"), 22725635); // TODO: remove the specific block
        dss = MCD.loadFromChainlog(CHAINLOG);
        pauseProxy = dss.chainlog.getAddress("MCD_PAUSE_PROXY");
        conv = ConvLike(address(RateSetter(dss.chainlog.getAddress("MCD_SPBEAM")).conv()));

        clip = address(new ClipMock(ILK));
        YUsdsInstance memory inst = YUsdsDeploy.deploy(address(this), pauseProxy, clip);
        yusds = YUsds(inst.yUsds);

        YUsdsConfig memory conf = YUsdsConfig({
            clip : clip,
            syr  : 1000000001547125957863212448,
            cap  : type(uint256).max,
            line : type(uint256).max
        });
        vm.startPrank(pauseProxy);
        YUsdsInit.init(dss, inst, conf);
        vm.stopPrank();

        // TODO: replace with deploy and init scripts
        rateSetter = new RateSetter(address(dss.jug), address(yusds), address(conv));
        rateSetter.rely(pauseProxy);
        rateSetter.deny(address(this));

        vm.startPrank(pauseProxy);
        dss.jug.rely(address(rateSetter));
        yusds.rely(address(rateSetter));

        // Configure global parameters
        rateSetter.file("tau", 0);
        rateSetter.file("maxLine", 1e9 * RAD);
        rateSetter.file("maxCap",  1e9 * WAD);

        rateSetter.file(ILK, "max", uint16(3000));
        rateSetter.file(ILK, "min", uint16(1));
        rateSetter.file(ILK, "step", uint16(100));

        rateSetter.file(SYR, "max", uint16(3000));
        rateSetter.file(SYR, "min", uint16(1));
        rateSetter.file(SYR, "step", uint16(100));

        // Authorize bud
        rateSetter.kiss(bud);
        vm.stopPrank();
    }

    function _duty() internal view returns (uint256 duty){
        (duty, ) = dss.jug.ilks(ILK);
    }

    function _dutyBps() internal view returns (uint256 dutyBps) {
        dutyBps = conv.rtob(_duty());
    }

    function _syrBps() internal view returns (uint256 syrBps) {
        syrBps = conv.rtob(yusds.syr());
    }

    function _currentBps() internal view returns (uint256 syrBps, uint256 dutyBps) {
        syrBps  = _syrBps();
        dutyBps = _dutyBps();
    }

    function test_constructor_and_init() public view {
        assertEq(address(rateSetter.jug()), address(dss.jug));
        assertEq(address(rateSetter.yusds()), address(yusds));
        assertEq(address(rateSetter.conv()), address(conv));
        assertEq(rateSetter.engineIlk(), ILK);

        // init
        assertEq(rateSetter.wards(address(this)), 0);
        assertEq(rateSetter.wards(pauseProxy), 1);
        //assertEq(rateSetter.wards(address(mom)), 1);
        //assertEq(mom.authority(), dss.chainlog.getAddress("MCD_ADM"));
        assertEq(dss.jug.wards(address(rateSetter)), 1);
        assertEq(yusds.wards(address(rateSetter)), 1);

        // TODO: check if need more checks once init scripts are done (e.g. bud kiss check)
    }

    function test_auth() public {
        checkAuth(address(rateSetter), "RateSetter");
    }

    function test_auth_methods() public {
        checkModifier(address(rateSetter), "RateSetter/not-authorized", [RateSetter.kiss.selector, RateSetter.diss.selector]);
    }

    function test_toll_methods() public {
        checkModifier(address(rateSetter), "RateSetter/not-facilitator", [RateSetter.set.selector]);
    }

    function test_good_methods() public {
        vm.startPrank(pauseProxy);
        rateSetter.file("bad", 1);
        rateSetter.kiss(address(this));
        vm.stopPrank();

        checkModifier(address(rateSetter), "RateSetter/module-halted", [RateSetter.set.selector]);
    }

    function test_kiss() public {
        address who = address(0x0ddaf);
        assertEq(rateSetter.buds(who), 0);

        vm.expectEmit(true, true, true, true);
        emit Kiss(who);
        vm.prank(pauseProxy); rateSetter.kiss(who);
        assertEq(rateSetter.buds(who), 1);
    }

    function test_diss() public {
        address who = address(0x0ddaf);
        vm.prank(pauseProxy); rateSetter.kiss(who);
        assertEq(rateSetter.buds(who), 1);

        vm.expectEmit(true, true, true, true);
        emit Diss(who);
        vm.prank(pauseProxy); rateSetter.diss(who);
        assertEq(rateSetter.buds(who), 0);
    }

    function test_file() public {
        checkFileUint(address(rateSetter), "RateSetter", ["bad", "tau", "toc", "maxLine", "maxCap"]);

        vm.startPrank(pauseProxy);

        vm.expectRevert("RateSetter/invalid-bad-value");
        rateSetter.file("bad", 2);

        vm.expectRevert("RateSetter/invalid-tau-value");
        rateSetter.file("tau", uint256(type(uint64).max) + 1);

        vm.expectRevert("RateSetter/invalid-toc-value");
        rateSetter.file("toc", uint256(type(uint128).max) + 1);

        vm.expectRevert("RateSetter/maxLine-insane-value");
        rateSetter.file("maxLine", RAD);

        vm.expectRevert("RateSetter/maxCap-insane-value");
        rateSetter.file("maxCap", 1e27 * WAD);

        vm.stopPrank();

        vm.expectRevert("RateSetter/not-authorized");
        rateSetter.file("bad", 1);
    }

    function test_file_ilk() public {
        (uint16 min, uint16 max, uint16 step) = rateSetter.dutyCfg();
        assertEq(min, 1);
        assertEq(max, 3000);
        assertEq(step, 100);

        vm.startPrank(pauseProxy);

        vm.expectEmit(true, true, true, true);
        emit File(ILK, "min", 100);
        rateSetter.file(ILK, "min", 100);
        rateSetter.file(ILK, "max", 3000);
        rateSetter.file(ILK, "step", 420);
        vm.stopPrank();

        (min, max, step) = rateSetter.dutyCfg();
        assertEq(min, 100);
        assertEq(max, 3000);
        assertEq(step, 420);
    }

    function test_file_syr() public {
        (uint16 min, uint16 max, uint16 step) = rateSetter.syrCfg();
        assertEq(min, 1);
        assertEq(max, 3000);
        assertEq(step, 100);

        vm.startPrank(pauseProxy);

        vm.expectEmit(true, true, true, true);
        emit File(SYR, "min", 100);
        rateSetter.file(SYR, "min", 100);
        rateSetter.file(SYR, "max", 3000);
        rateSetter.file(SYR, "step", 420);
        vm.stopPrank();

        (min, max, step) = rateSetter.syrCfg();
        assertEq(min, 100);
        assertEq(max, 3000);
        assertEq(step, 420);
    }

    function test_revert_file_invalid() public {
        vm.startPrank(pauseProxy);
        (uint16 min, uint16 max,) = rateSetter.dutyCfg();

        vm.expectRevert("RateSetter/min-too-high");
        rateSetter.file(ILK, "min", max + 1);

        vm.expectRevert("RateSetter/max-too-low");
        rateSetter.file(ILK, "max", min - 1);

        vm.expectRevert("RateSetter/file-unrecognized-param");
        rateSetter.file(ILK, "unknown", 100);

        vm.expectRevert("RateSetter/invalid-value");
        rateSetter.file(ILK, "max", uint256(type(uint16).max) + 1);

        vm.expectRevert("RateSetter/file-unrecognized-id");
        rateSetter.file("MOG-A", "min", 100);

        vm.stopPrank();

        vm.expectRevert("RateSetter/not-authorized");
        rateSetter.file(ILK, "min", 100);
    }

    function test_set() public {
        (uint256 syrTarget, uint256 dutyTarget) = (_syrBps() + 50, _dutyBps() + 50);

        vm.expectEmit(true, true, true, true);
        emit Set(syrTarget, dutyTarget, 50_000_000 * RAD, 50_000_000 * WAD);
        vm.prank(bud); rateSetter.set(syrTarget, dutyTarget, 50_000_000 * RAD, 50_000_000 * WAD);

        assertEq(yusds.syr(), conv.btor(syrTarget));
        assertEq(_duty(), conv.btor(dutyTarget));
        assertEq(yusds.line(), 50_000_000 * RAD);
        assertEq(yusds.cap(), 50_000_000 * WAD);
    }

    // checks that can still set rates, even if previously the rates were outside of the range
    function test_set_rate_outside_range() public {
        // rate above max
        dss.jug.drip(ILK);
        vm.startPrank(pauseProxy);
        dss.jug.file(ILK, "duty", conv.btor(3050)); // outside range
        yusds.file("syr", conv.btor(3050)); // outside range
        vm.stopPrank();

        vm.startPrank(bud);
        rateSetter.set(2999, 2999, 0, 0);
        vm.stopPrank();

        assertEq(_duty(), conv.btor(2999));
        assertEq(yusds.syr(), conv.btor(2999));

        // rate below min
        dss.jug.drip(ILK);
        yusds.drip();
        vm.startPrank(pauseProxy);
        dss.jug.file(ILK, "duty", conv.btor(0)); // outside range
        yusds.file("syr", conv.btor(0)); // outside range
        vm.stopPrank();

        vm.startPrank(bud);
        rateSetter.set(50, 50, 0, 0);
        vm.stopPrank();

        assertEq(_duty(), conv.btor(50));
        assertEq(yusds.syr(), conv.btor(50));
    }

    function test_revert_set_syr_not_configured_rate() public {
        vm.prank(pauseProxy); rateSetter.file(SYR, "step", 0);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/rate-not-configured");
        vm.prank(bud); rateSetter.set(syrBps, dutyBps, 0, 0);
    }

    function test_revert_set_duty_not_configured_rate() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "step", 0);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/rate-not-configured");
        vm.prank(bud); rateSetter.set(syrBps, dutyBps, 0, 0);
    }

    function test_revert_set_duty_below_min() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "min", 100);
        uint256 syrBps = _syrBps();
        vm.expectRevert("RateSetter/below-min");
        vm.prank(bud); rateSetter.set(syrBps, 50, 0, 0);
    }

    function test_revert_set_syr_below_min() public {
        vm.prank(pauseProxy); rateSetter.file(SYR, "min", 100);
        uint256 dutyBps = _dutyBps();
        vm.expectRevert("RateSetter/below-min");
        vm.prank(bud); rateSetter.set(50, dutyBps, 0, 0);
    }

    function test_revert_set_duty_above_max() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "max", 100);
        uint256 syrBps = _syrBps();
        vm.expectRevert("RateSetter/above-max");
        vm.prank(bud); rateSetter.set(syrBps, 150, 0, 0);
    }

    function test_revert_set_syr_above_max() public {
        vm.prank(pauseProxy); rateSetter.file(SYR, "max", 100);
        uint256 dutyBps = _dutyBps();
        vm.expectRevert("RateSetter/above-max");
        vm.prank(bud); rateSetter.set(150, dutyBps, 0, 0);
    }

    function test_revert_set_duty_delta_above_step() public {
        vm.prank(pauseProxy); rateSetter.file(ILK, "step", 100);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/delta-above-step");
        vm.prank(bud); rateSetter.set(syrBps, dutyBps + 101, 0, 0);
    }

    function test_revert_set_syr_delta_above_step() public {
        vm.prank(pauseProxy); rateSetter.file(SYR, "step", 100);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/delta-above-step");
        vm.prank(bud); rateSetter.set(syrBps + 101, dutyBps, 0, 0);
    }

    function test_revert_line_too_high() public {
        vm.prank(pauseProxy); rateSetter.file("maxLine", 100 * RAD);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/line-too-high");
        vm.prank(bud); rateSetter.set(syrBps, dutyBps, 100 * RAD + 1, 0);
    }

    function test_revert_cap_too_high() public {
        vm.prank(pauseProxy); rateSetter.file("maxCap", 100 * WAD);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/cap-too-high");
        vm.prank(bud);
        rateSetter.set(syrBps, dutyBps, 0, 100 * WAD + 1);
    }

    function test_revert_set_before_cooldown() public {
        vm.prank(pauseProxy); rateSetter.file("tau", 100);
        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.prank(bud); rateSetter.set(syrBps, dutyBps, 0, 0);

        vm.warp(block.timestamp + 99);

        vm.expectRevert("RateSetter/too-early");
        vm.prank(bud); rateSetter.set(syrBps, dutyBps, 0, 0);
    }

    function test_revert_set_malfunctioning_conv() public {
        // TODO: replace with deploy and init scripts
        RateSetter rateSetter2 = new RateSetter(address(dss.jug), address(yusds), address(new MockBrokenConv(address(conv))));
        rateSetter2.rely(pauseProxy);
        rateSetter2.deny(address(this));

        vm.startPrank(pauseProxy);
        dss.jug.rely(address(rateSetter2));
        yusds.rely(address(rateSetter2));

        // Configure global parameters
        rateSetter2.file("tau", 0);
        rateSetter2.file("maxLine", 1e9 * RAD);
        rateSetter2.file("maxCap",  1e9 * WAD);

        rateSetter2.file(ILK, "max", uint16(3000));
        rateSetter2.file(ILK, "min", uint16(1));
        rateSetter2.file(ILK, "step", uint16(100));

        rateSetter2.file(SYR, "max", uint16(3000));
        rateSetter2.file(SYR, "min", uint16(1));
        rateSetter2.file(SYR, "step", uint16(100));

        // Authorize bud
        rateSetter2.kiss(bud);
        vm.stopPrank();

        (uint256 syrBps, uint256 dutyBps) = _currentBps();
        vm.expectRevert("RateSetter/invalid-rate-conv");
        vm.prank(bud); rateSetter2.set(syrBps, dutyBps, 0, 0);
    }
}
