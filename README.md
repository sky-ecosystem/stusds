# Yield USDS

An implementation of a yield-bearing USDS token, which aims at ensuring that all SKY-backed borrowing is funded by segregated risk capital.
Depositors take on several risks, such as stake engine bad debt accrual, or Sky governance risk (see `Trust Assumptions and Suppliers Considerations` below).

## Overview

Users can deposit USDS to mint yUSDS up to a defined global cap.

Users can redeem their yUSDS to USDS, as long as there is enough withdrawable USDS, which is determined by:
* Total deposited funds and accrued yield.
* Existing stake engine debt.
* Amount of USDS currently in auction (disregarding the liquidation penalty).
* Amount of stake engine bad debt, which was written off when concluding past auctions.
* Past governance slashing operations. 

The yUSDS contract sets the stake engine debt ceiling dynamically, as part of its different actions.

Conversely, the yUSDS supply rate and stake engine borrow rate are set asynchronously through privileged configurations (`file()`).
Those configurations are managed through the RateSetter contract, which allows governance-configured operators to set the params, with some security restrictions.

Similarly, the RateSetter also sets the yUSDS supply cap and max debt ceiling, also with some governance-configured limitations. 

The yUSDS contract supports ERC4626. It uses the ERC-1822 UUPS pattern for upgradeability and the ERC-1967 proxy storage slots standard.
It is important that the `YUsdsDeploy` library sequence be used for deploying.

#### OZ upgradeability validations

The OZ validations can be run alongside the existing tests:  
`VALIDATE=true forge test --ffi --build-info --extra-output storageLayout`

## Referral Code

The `deposit` and `mint` functions accept an optional `uint16 referral` parameter that frontends can use to mark deposits as originating from them. Such deposits emit a `Referral(uint16 indexed referral, address indexed owner, uint256 assets, uint256 shares)` event. This could be used to implement a revshare campaign, in which case the off-chain calculation scheme will likely need to keep track of any `Transfer` and `Withdraw` events following a `Referral` for a given token owner.

## Notes, Disclaimers and Known Issues:

### Trust Assumptions and Suppliers Considerations:
* It is assumed the `cut` can be called from the clipper when bad debt is accrued, or by governance.
* yUSDS suppliers trust Sky governance. For example, if it desires, governance could slash everything (or upgrade the contract), and possibly during the gov delay period all funds are borrowed, so withdrawing is not possible.
* yUSDS suppliers should also be aware that operators of the Rate Setter (appointed by governance) can set rates in a way that all funds are borrowed, so it is up to governance to make sure that over time they aim to allow withdrawals.
* The yUSDS system does not use the debt ceiling Instant Access Module (aka autoline), but instead allows the deposit and withdraw code to set the `line` to any value under the max borrow line. This means that in specific situations the borrowed amount can move very fast. In practice, it implies that yUSDS depositors also take the risk for oracles reporting a very high price and allowing minting of "cheap" usds, which the autoline usually mitigates against with it's pacing.
* The desirable status in the system is that the non-withdrawable amount backs the stake engine debt, but there is nothing preventing yUSDS redeems of the other funds. There is a likely possibility that these other funds will be withdrawn when people speculate that bad debt will be created, or see that a governance action to slash is coming. If it's clear that slashing is going to happen then we can even expect all withdrawable funds to be pulled. This can create large swings in the deposit amount, and also prevent the bad debt from being better socialized. This needs to be taken into account by suppliers.
* Deposits could be griefed by other deposits (because of the cap). Withdrawals could be griefed by borrowers. Borrows could be griefed by suppliers. These scenarios are assumed to be mitigated by the option to use flashbots and by the economic cost of such griefing for a long period.
* Note that not being able to redeem all yUSDS instantly, and slashing due to bad debt accrual, might bring a risk of depeg/devaluation on other markets. 3rd-party integrations should be aware of this risk.

### Accounting:
* In general the system aims to maintain a status where the supplied funds including accruals always back the debt. However this is not guaranteed (for example because of stability fee accrual or past `cut` operations).
* The supply cap is assumed to mitigate against large protocol losses for temporary cases where  the combination of supply rate and deposits outweighs the borrow rates and borrows.
* It is assumed that in case of migration to a new stake engine and/or a new clipper, the accounting of both the old contracts and the new ones will be examined as part of the process.

### Rate Setter:
* The Rate Setter logic is based on [SPBEAM](https://github.com/sky-ecosystem/sp-beam). Its various security considerations are assumed here as well (e.g "Asymmetrical Risks Between Rate Increase and Decrease", "Considerations for Configurations", see SPBEAM audit [reports](https://github.com/sky-ecosystem/sp-beam/tree/master/audits).
* There is no pacing mechanism for the Rate Setter's `cap` and `line` setting, as it is assumed that the combination of the max values and the rate pacing ("steps") are enough to protect against big losses.
* The Rate Setter operators off-chain algorithm is assumed to take into account manipulation attempts. For example, it can use an average past utilization, and possibly introduce some variance in its samples. If needed, it is assumed to be updated when manipulations are spotted.
* It is assumed that a max rate of 50% is enough (as supported in the [Conv](https://github.com/sky-ecosystem/rates-conv) module). If needed, the Rate Setter could be replaced to support higher rates.
* The Rate Setter is assumed to have one `bud` for all practical use cases. If another bud is added, it is assumed to be done carefully after examining front-running, collidings and collusions.

## Shutdown

The implementation assumes Maker emergency shutdown can not be triggered. Any system shutdown should be orchestrated by Maker governance.

## Copyright

The original code was created by hexonaut (SavingsDai) and the MakerDAO devs (Pot).
Since it should belong to the MakerDAO community the Copyright for the code has been transferred to Dai Foundation

