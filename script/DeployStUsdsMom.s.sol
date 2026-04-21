// SPDX-FileCopyrightText: 2026 Dai Foundation <www.daifoundation.org>
// SPDX-License-Identifier: AGPL-3.0-or-later

pragma solidity ^0.8.21;

import { Script } from "forge-std/Script.sol";
import { console2 } from "forge-std/console2.sol";

import { ChainlogAbstract } from "dss-interfaces/dss/ChainlogAbstract.sol";

import { StUsdsMom } from "src/StUsdsMom.sol";
import { StUsdsDeploy } from "deploy/StUsdsDeploy.sol";

contract DeployStUsdsMom is Script {
    address internal constant CHAINLOG = 0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F;

    function run() external returns (address mom) {
        ChainlogAbstract chainlog = ChainlogAbstract(CHAINLOG);

        address stUsds = chainlog.getAddress("STUSDS");
        address owner = vm.envOr("STUSDS_MOM_OWNER", chainlog.getAddress("MCD_PAUSE_PROXY"));

        console2.log("Deploying StUsdsMom");
        console2.log("Chain id:", block.chainid);
        console2.log("stUSDS:", stUsds);
        console2.log("Owner:", owner);
        console2.log("Current STUSDS_MOM:", chainlog.getAddress("STUSDS_MOM"));

        vm.startBroadcast();
        mom = StUsdsDeploy.deployMom(owner);
        vm.stopBroadcast();

        StUsdsMom deployed = StUsdsMom(mom);
        require(address(deployed.stusds()) == stUsds, "DeployStUsdsMom/stusds-mismatch");
        require(deployed.owner() == owner, "DeployStUsdsMom/owner-mismatch");
        require(deployed.authority() == address(0), "DeployStUsdsMom/authority-not-zero");

        console2.log("New STUSDS_MOM:", mom);
    }
}
