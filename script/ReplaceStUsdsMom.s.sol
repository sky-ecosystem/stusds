// SPDX-FileCopyrightText: 2026 Dai Foundation <www.daifoundation.org>
// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.21;

import { Script } from "forge-std/Script.sol";
import { console2 } from "forge-std/console2.sol";

import { ChainlogAbstract } from "dss-interfaces/dss/ChainlogAbstract.sol";
import { DssInstance, MCD } from "dss-test/MCD.sol";

import { StUsdsMom } from "src/StUsdsMom.sol";
import { StUsdsDeploy } from "deploy/StUsdsDeploy.sol";
import { StUsdsInit } from "deploy/StUsdsInit.sol";

interface WardsLike {
    function wards(address) external view returns (uint256);
}

contract ReplaceStUsdsMom is Script {
    address internal constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    function run() external returns (address newMom) {
        ChainlogAbstract chainlog = ChainlogAbstract(CHAINLOG);
        DssInstance memory dss = MCD.loadFromChainlog(CHAINLOG);

        address executor = vm.envOr("STUSDS_MOM_EXECUTOR", chainlog.getAddress("MCD_PAUSE_PROXY"));
        address stUsds = chainlog.getAddress("STUSDS");
        address rateSetter = chainlog.getAddress("STUSDS_RATE_SETTER");
        address oldMom = chainlog.getAddress("STUSDS_MOM");
        address chief = chainlog.getAddress("MCD_ADM");

        newMom = vm.envOr("NEW_STUSDS_MOM", address(0));

        console2.log("Replacing STUSDS_MOM");
        console2.log("Chain id:", block.chainid);
        console2.log("Executor:", executor);
        console2.log("stUSDS:", stUsds);
        console2.log("Rate setter:", rateSetter);
        console2.log("Chief:", chief);
        console2.log("Old STUSDS_MOM:", oldMom);

        if (newMom == address(0)) {
            console2.log("NEW_STUSDS_MOM not set; deploying a new StUsdsMom");

            vm.startBroadcast(executor);
            newMom = StUsdsDeploy.deployMom(executor);
            vm.stopBroadcast();

            console2.log("New STUSDS_MOM deployed:", newMom);
        } else {
            console2.log("Using existing NEW_STUSDS_MOM:", newMom);
        }

        require(newMom != oldMom, "ReplaceStUsdsMom/same-mom");
        require(address(StUsdsMom(newMom).stusds()) == stUsds, "ReplaceStUsdsMom/stusds-mismatch");
        require(StUsdsMom(newMom).owner() == executor, "ReplaceStUsdsMom/new-mom-owner-not-executor");
        require(StUsdsMom(oldMom).owner() == executor, "ReplaceStUsdsMom/old-mom-owner-not-executor");

        vm.startBroadcast(executor);
        StUsdsInit.replaceMom(dss, newMom);
        vm.stopBroadcast();

        require(chainlog.getAddress("STUSDS_MOM") == newMom, "ReplaceStUsdsMom/chainlog-not-updated");
        require(WardsLike(stUsds).wards(newMom) == 1, "ReplaceStUsdsMom/stusds-new-mom-not-ward");
        require(WardsLike(rateSetter).wards(newMom) == 1, "ReplaceStUsdsMom/rate-setter-new-mom-not-ward");
        require(StUsdsMom(newMom).authority() == chief, "ReplaceStUsdsMom/new-mom-authority-not-chief");
        require(WardsLike(stUsds).wards(oldMom) == 0, "ReplaceStUsdsMom/stusds-old-mom-still-ward");
        require(WardsLike(rateSetter).wards(oldMom) == 0, "ReplaceStUsdsMom/rate-setter-old-mom-still-ward");
        require(StUsdsMom(oldMom).authority() == address(0), "ReplaceStUsdsMom/old-mom-authority-not-zero");
        require(StUsdsMom(oldMom).owner() == address(0), "ReplaceStUsdsMom/old-mom-owner-not-zero");

        console2.log("STUSDS_MOM replaced:", newMom);
    }
}
