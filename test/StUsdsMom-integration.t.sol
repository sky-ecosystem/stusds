// SPDX-FileCopyrightText: 2026 Dai Foundation <www.daifoundation.org>
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

import { DSTokenAbstract } from "dss-interfaces/Interfaces.sol";
import { StUsds } from "src/StUsds.sol";
import { StUsdsMom } from "src/StUsdsMom.sol";
import { StUsdsRateSetter } from "src/StUsdsRateSetter.sol";
import { StUsdsInit } from "deploy/StUsdsInit.sol";
import { StUsdsDeploy } from "deploy/StUsdsDeploy.sol";

interface ChiefLike {
    function hat() external view returns (address);
}

interface LockStakeEngineLike {
    function draw(address owner, uint256 index, address to, uint256 wad) external;
    function ilk() external view returns (bytes32);
    function lock(address owner, uint256 index, uint256 wad, uint16 ref) external;
    function open(uint256 index) external returns (address urn);
}

contract StUsdsMomIntegrationTest is DssTest {
    address constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    DssInstance         dss;
    ChiefLike           chief;
    LockStakeEngineLike engine;
    DSTokenAbstract     sky;
    StUsdsRateSetter    rateSetter;
    StUsds              stusds;
    StUsdsMom           oldMom;
    StUsdsMom           mom;
    address             pauseProxy;

    bytes32 ilk;

    event Draw(address indexed owner, uint256 indexed index, address to, uint256 wad);
    event Drip(uint256 chi, uint256 diff);
    event ZeroLine(address indexed rateSetter);

    function setUp() public {
        vm.createSelectFork(vm.envString("ETH_RPC_URL"));

        dss = MCD.loadFromChainlog(CHAINLOG);
        chief = ChiefLike(dss.chainlog.getAddress("MCD_ADM"));

        pauseProxy = dss.chainlog.getAddress("MCD_PAUSE_PROXY");
        engine     = LockStakeEngineLike(dss.chainlog.getAddress("LOCKSTAKE_ENGINE"));
        sky        = DSTokenAbstract(dss.chainlog.getAddress("SKY"));
        stusds     = StUsds(dss.chainlog.getAddress("STUSDS"));
        rateSetter = StUsdsRateSetter(dss.chainlog.getAddress("STUSDS_RATE_SETTER"));
        oldMom     = StUsdsMom(dss.chainlog.getAddress("STUSDS_MOM"));

        ilk = stusds.ilk();

        vm.prank(pauseProxy);
        mom = StUsdsMom(StUsdsDeploy.deployMom(pauseProxy));

        assertEq(mom.owner(), pauseProxy);
        assertEq(mom.authority(), address(0));
        assertEq(address(mom.stusds()), address(stusds));
        assertEq(ilk, engine.ilk());

        vm.startPrank(pauseProxy);
        StUsdsInit.replaceMom(
            dss,
            address(mom)
        );
        vm.stopPrank();

        assertEq(stusds.wards(address(mom)), 1);
        assertEq(rateSetter.wards(address(mom)), 1);
        assertEq(mom.authority(), dss.chainlog.getAddress("MCD_ADM"));
        assertEq(dss.chainlog.getAddress("STUSDS_MOM"), address(mom));
        assertEq(mom.owner(), pauseProxy);

        assertNotEq(address(oldMom), address(mom));

        assertEq(stusds.wards(address(oldMom)), 0);
        assertEq(rateSetter.wards(address(oldMom)), 0);
        assertEq(oldMom.authority(), address(0));
        assertEq(oldMom.owner(), address(0));
    }

    // Expose the StUsdsInit library path through an external call, so revert
    // assertions can target `replaceMom()`.
    function __replaceMomHelper(address newMom) external {
        StUsdsInit.replaceMom(dss, newMom);
    }

    function testRevertReplaceMomWithSameMom() public {
        vm.expectRevert("StUsdsInit/same-mom");
        this.__replaceMomHelper(address(mom));
    }

    function testRevertWrongStUsds() public {
        StUsdsMom badMom = new StUsdsMom(address(0x01));
        vm.expectRevert("StUsdsInit/stusds-does-not-match");
        this.__replaceMomHelper(address(badMom));
    }

    function _checkZeroLine(address who) internal {
        vm.expectEmit(false, false, false, false, address(stusds));
        emit Drip(0,0);
        vm.expectEmit(true, true, true, true);
        emit ZeroLine(address(rateSetter));

        vm.prank(who);
        mom.zeroLine(address(rateSetter));

        assertEq(stusds.line(), 0);
        assertEq(rateSetter.maxLine(), 0);
    }

    function _art(bytes32 ilk_, address urn) internal view returns (uint256 art) {
        (, art) = dss.vat.urns(ilk_, urn);
    }

    function _rate(bytes32 ilk_) internal view returns (uint256 rate) {
        (, rate,,,) = dss.vat.ilks(ilk_);
    }

    function _lockOnStakeEngine() internal returns (address urn) {
        uint256 lockAmount = 3_000_000 * WAD;
        deal(address(sky), address(this), lockAmount, true);
        urn = engine.open(0);
        sky.approve(address(engine), lockAmount);
        engine.lock(address(this), 0, lockAmount, 5);
        assertEq(_art(ilk, urn), 0);
    }

    function testRevertDrawAfterZeroLineHat() public {
        _lockOnStakeEngine();
        _checkZeroLine(chief.hat());
        uint256 borrowAmount = 40_000 * WAD;
        vm.expectRevert("Vat/ceiling-exceeded");
        engine.draw(address(this), 0, address(this), borrowAmount);
    }

    function testRevertDrawAfterZeroLineOwner() public {
        _lockOnStakeEngine();
        _checkZeroLine(pauseProxy);
        uint256 borrowAmount = 40_000 * WAD;
        vm.expectRevert("Vat/ceiling-exceeded");
        engine.draw(address(this), 0, address(this), borrowAmount);
    }
}
