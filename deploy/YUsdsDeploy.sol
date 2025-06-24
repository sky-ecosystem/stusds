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
import { YUsdsRateSetter } from "src/YUsdsRateSetter.sol";
import { YUsdsMom } from "src/YUsdsMom.sol";
import { YUsdsInstance } from "./YUsdsInstance.sol";

interface SPBEAMLike {
    function conv() external view returns (address);
}

library YUsdsDeploy {
    function deploy(
        address deployer,
        address owner,
        address clip
    ) internal returns (YUsdsInstance memory instance) {
        ChainlogAbstract chainlog = ChainlogAbstract(0xdA0Ab1e0017DEbCd72Be8599041a2aa3bA7e740F);

        address _yUsdsImp = address(new YUsds(
                                            chainlog.getAddress("USDS_JOIN"),
                                            chainlog.getAddress("MCD_JUG"),
                                            clip,
                                            chainlog.getAddress("MCD_VOW")
                                        )
                                    );
        address _yUsds = address(new ERC1967Proxy(_yUsdsImp, abi.encodeCall(YUsds.initialize, ())));
        ScriptTools.switchOwner(_yUsds, deployer, owner);

        address _rateSetter = address(new YUsdsRateSetter(
            _yUsds,
            SPBEAMLike(chainlog.getAddress("MCD_SPBEAM")).conv()
        ));
        ScriptTools.switchOwner(_rateSetter, deployer, owner);

        YUsdsMom _mom = new YUsdsMom(_yUsds);
        _mom.setOwner(owner);

        instance.yUsds      = _yUsds;
        instance.yUsdsImp   = _yUsdsImp;
        instance.rateSetter = _rateSetter;
        instance.mom        = address(_mom);
    }
}
