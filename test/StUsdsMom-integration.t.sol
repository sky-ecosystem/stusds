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

interface ChiefLike {
    function hat() external view returns (address);
}

interface LockStakeEngineLike {
    function draw(address owner, uint256 index, address to, uint256 wad) external;
    function ilk() external view returns (bytes32);
    function lock(address owner, uint256 index, uint256 wad, uint16 ref) external;
    function open(uint256 index) external returns (address urn);
}

interface UsdsLike {
    function balanceOf(address) external view returns (uint256);
}

contract StUsdsMomIntegrationTest is DssTest {
    address constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    DssInstance         dss;
    ChiefLike           chief;
    LockStakeEngineLike engine;
    UsdsLike            usds;
    DSTokenAbstract     sky;
    StUsdsRateSetter    rateSetter;
    StUsds              stusds;
    StUsdsMom           mom;
    address             pauseProxy;

    bytes32 ilk;

    address bud = address(0xb0d);
    address bud2 = address(0xb0d2);

    event Draw(address indexed owner, uint256 indexed index, address to, uint256 wad);
    event ZeroLine(address indexed rateSetter);

    function setUp() public {
        vm.createSelectFork(vm.envString("ETH_RPC_URL"));

        dss = MCD.loadFromChainlog(CHAINLOG);
        chief = ChiefLike(dss.chainlog.getAddress("MCD_ADM"));

        pauseProxy = dss.chainlog.getAddress("MCD_PAUSE_PROXY");
        engine = LockStakeEngineLike(dss.chainlog.getAddress("LOCKSTAKE_ENGINE"));
        usds = UsdsLike(dss.chainlog.getAddress("USDS"));
        sky = DSTokenAbstract(dss.chainlog.getAddress("SKY"));
        stusds = StUsds(dss.chainlog.getAddress("STUSDS"));
        rateSetter = StUsdsRateSetter(dss.chainlog.getAddress("STUSDS_RATE_SETTER"));

        vm.prank(pauseProxy);
        mom = new StUsdsMom(address(stusds));

        ilk = stusds.ilk();

        address[] memory buds = new address[](2);
        buds[0] = bud;
        buds[1] = bud2;

        vm.startPrank(pauseProxy);
        for (uint256 i; i < buds.length; i ++) {
            rateSetter.kiss(buds[i]);
        }
        stusds.rely(address(mom));
        rateSetter.rely(address(mom));
        mom.setAuthority(dss.chainlog.getAddress("MCD_ADM"));
        vm.stopPrank();
    }

    function testSetupIsCorrect() public view {
        assertEq(ilk, engine.ilk());
        assertEq(stusds.wards(address(mom)), 1);
        assertEq(rateSetter.wards(address(mom)), 1);
        assertEq(mom.authority(), dss.chainlog.getAddress("MCD_ADM"));
    }

    function _checkZeroLine(address who) internal {
        vm.prank(who);
        vm.expectEmit(true, true, true, true);
        emit ZeroLine(address(rateSetter));
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

    function _zeroLineAsHat() internal {
        _checkZeroLine(chief.hat());
    }

    function _zeroLineAsOwner() internal {
        _checkZeroLine(pauseProxy);
    }

    function _lockOnStakeEngine() internal returns (address urn) {
        deal(address(sky), address(this), 3_000_000 * 10**18, true);
        urn = engine.open(0);
        sky.approve(address(engine), 3_000_000 * 10**18);
        engine.lock(address(this), 0, 3_000_000 * 10**18, 5);
        assertEq(_art(ilk, urn), 0);
    }

    function testDrawLockStake() public {
        address urn = _lockOnStakeEngine();
        vm.expectEmit(true, true, true, true);
        emit Draw(address(this), 0, address(this), 40_000 * 10**18);
        engine.draw(address(this), 0, address(this), 40_000 * 10**18);
        assertApproxEqAbs(_art(ilk, urn) * _rate(ilk) / RAY, 40_000 * 10**18, 1);
        assertEq(usds.balanceOf(address(this)), 40_000 * 10**18);
    }

    function testRevertDrawAfterZeroLineHat() public {
        _lockOnStakeEngine();
        _zeroLineAsHat();
        vm.expectRevert("Vat/ceiling-exceeded");
        engine.draw(address(this), 0, address(this), 40_000 * 10**18);
    }

    function testRevertDrawAfterZeroLineOwner() public {
        _lockOnStakeEngine();
        _zeroLineAsOwner();
        vm.expectRevert("Vat/ceiling-exceeded");
        engine.draw(address(this), 0, address(this), 40_000 * 10**18);
    }
}
