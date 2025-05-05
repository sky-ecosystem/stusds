// SPDX-License-Identifier: AGPL-3.0-or-later

// Copyright (C) 2021 Dai Foundation
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

import { ScriptTools } from "dss-test/ScriptTools.sol";
import { ERC1967Proxy } from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol";

import "dss-interfaces/Interfaces.sol";

import { YUsds } from "src/YUsds.sol";

import { YUsdsInstance } from "./YUsdsInstance.sol";

library YUsdsDeploy {
    function deploy(
        address deployer,
        address owner
    ) internal returns (YUsdsInstance memory instance) {
        ChainlogAbstract chainlog = ChainlogAbstract(0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F);

        address _yUsdsImp = address(new YUsds(
                                            chainlog.getAddress("USDS_JOIN"),
                                            chainlog.getAddress("MCD_JUG"),
                                            chainlog.getAddress("MCD_DOG"),
                                            chainlog.getAddress("MCD_VOW"),
                                            "LSEV2-SKY-A"
                                        )
                                    );
        address _yUsds = address(new ERC1967Proxy(_yUsdsImp, abi.encodeCall(YUsds.initialize, ())));
        ScriptTools.switchOwner(_yUsds, deployer, owner);

        instance.yUsds    = _yUsds;
        instance.yUsdsImp = _yUsdsImp;
    }
}
