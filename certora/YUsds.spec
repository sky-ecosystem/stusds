// YUsds.spec

using Vat as vat;
using Jug as jug;
using UsdsMock as usds;
using SignerMock as signer;
using Auxiliar as aux;
using UsdsJoinMock as usdsJoin;

methods {
    // storage variables
    function wards(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function allowance(address, address) external returns (uint256) envfree;
    function nonces(address) external returns (uint256) envfree;
    function chi() external returns (uint192) envfree;
    function rho() external returns (uint64) envfree;
    function syr() external returns (uint256) envfree;
    function cap() external returns (uint256) envfree;
    // immutables
    function usds() external returns (address) envfree;
    function vow() external returns (address) envfree;
    function ilk() external returns (bytes32) envfree;
    //
    function DOMAIN_SEPARATOR() external returns (bytes32) envfree;
    function PERMIT_TYPEHASH() external returns (bytes32) envfree;
    //
    function vat.ilks(bytes32) external returns (uint256, uint256, uint256, uint256, uint256) envfree;
    function vat.wards(address) external returns (uint256) envfree;
    function vat.can(address, address) external returns (uint256) envfree;
    function vat.live() external returns (uint256) envfree;
    function vat.vice() external returns (uint256) envfree;
    function vat.debt() external returns (uint256) envfree;
    function vat.dai(address) external returns (uint256) envfree;
    function vat.sin(address) external returns (uint256) envfree;
    function jug.ilks(bytes32) external returns (uint256, uint256) envfree;
    function jug.vow() external returns (address) envfree;
    function jug.base() external returns (uint256) envfree;
    function usds.allowance(address, address) external returns (uint256) envfree;
    function usds.balanceOf(address) external returns (uint256) envfree;
    function usds.totalSupply() external returns (uint256) envfree;
    function aux.call_ecrecover(bytes32, uint8, bytes32, bytes32) external returns (address) envfree;
    function aux.computeDigestForToken(bytes32, bytes32, address, address, uint256, uint256, uint256) external returns (bytes32) envfree;
    function aux.signatureToVRS(bytes) external returns (uint8, bytes32, bytes32) envfree;
    function aux.VRSToSignature(uint8, bytes32, bytes32) external returns (bytes) envfree;
    function aux.size(bytes) external returns (uint256) envfree;
    function aux.rpow(uint256, uint256) external returns (uint256) envfree;
    //
    function _.isValidSignature(bytes32, bytes) external => DISPATCHER(true);
    function _.Due() external => DueSummary() expect uint256;
}

ghost uint256 Due;
function DueSummary() returns uint256 {
    return Due;
}

definition WAD() returns mathint = 10^18;
definition RAY() returns mathint = 10^27;
definition max_int256() returns mathint = 2^255 - 1;
definition _divup(mathint x, mathint y) returns mathint = x != 0 ? ((x - 1) / y) + 1 : 0;
definition _min(mathint x, mathint y) returns mathint = x < y ? x : y;
definition _subcap(mathint x, mathint y) returns mathint = x > y ? x - y : 0;

definition defNewChi(env e) returns mathint = e.block.timestamp > rho() ? aux.rpow(syr(), require_uint256(e.block.timestamp - rho())) * chi() / RAY() : chi();
definition defConvertToShares(env e, mathint assets) returns mathint = defNewChi(e) > 0 ? assets * RAY() / defNewChi(e) : 0; // The else path should provoke a revert
definition defConvertToAssets(env e, mathint shares) returns mathint = shares * defNewChi(e) / RAY();


ghost balanceSum() returns mathint {
    init_state axiom balanceSum() == 0;
}
hook Sstore balanceOf[KEY address a] uint256 balance (uint256 old_balance) {
    havoc balanceSum assuming balanceSum@new() == balanceSum@old() + balance - old_balance && balanceSum@new() >= 0;
}
invariant balanceSum_equals_totalSupply() balanceSum() == to_mathint(totalSupply())
            filtered {
                m -> m.selector != sig:upgradeToAndCall(address, bytes).selector
            }

// Verify no more entry points exist
rule entryPoints(method f) filtered { f -> !f.isView } {
    env e;

    calldataarg args;
    f(e, args);

    assert f.selector == sig:initialize().selector ||
           f.selector == sig:upgradeToAndCall(address,bytes).selector ||
           f.selector == sig:rely(address).selector ||
           f.selector == sig:deny(address).selector ||
           f.selector == sig:file(bytes32,uint256).selector ||
           f.selector == sig:cut(uint256).selector ||
           f.selector == sig:drip().selector ||
           f.selector == sig:transfer(address,uint256).selector ||
           f.selector == sig:transferFrom(address,address,uint256).selector ||
           f.selector == sig:approve(address,uint256).selector ||
           f.selector == sig:deposit(uint256,address).selector ||
           f.selector == sig:deposit(uint256,address,uint16).selector ||
           f.selector == sig:mint(uint256,address).selector ||
           f.selector == sig:mint(uint256,address,uint16).selector ||
           f.selector == sig:withdraw(uint256,address,address).selector ||
           f.selector == sig:redeem(uint256,address,address).selector ||
           f.selector == sig:permit(address,address,uint256,uint256,bytes).selector ||
           f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector;
}

// Verify that each storage layout is only modified in the corresponding functions
rule storageAffected(method f) filtered { f -> f.selector != sig:upgradeToAndCall(address,bytes).selector } {
    env e;

    address anyAddr;
    address anyAddr2;

    mathint wardsBefore = wards(anyAddr);
    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfBefore = balanceOf(anyAddr);
    mathint allowanceBefore = allowance(anyAddr, anyAddr2);
    mathint noncesBefore = nonces(anyAddr);
    mathint chiBefore = chi();
    mathint rhoBefore = rho();
    mathint syrBefore = syr();
    mathint capBefore = cap();

    calldataarg args;
    f(e, args);

    mathint wardsAfter = wards(anyAddr);
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfAfter = balanceOf(anyAddr);
    mathint allowanceAfter = allowance(anyAddr, anyAddr2);
    mathint noncesAfter = nonces(anyAddr);
    mathint chiAfter = chi();
    mathint rhoAfter = rho();
    mathint syrAfter = syr();
    mathint capAfter = cap();

    assert wardsAfter != wardsBefore             => f.selector == sig:initialize().selector ||
                                                    f.selector == sig:rely(address).selector ||
                                                    f.selector == sig:deny(address).selector, "Assert 1";
    assert totalSupplyAfter != totalSupplyBefore => f.selector == sig:deposit(uint256,address).selector ||
                                                    f.selector == sig:deposit(uint256,address,uint16).selector ||
                                                    f.selector == sig:mint(uint256,address).selector ||
                                                    f.selector == sig:mint(uint256,address,uint16).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector, "Assert 2";
    assert balanceOfAfter != balanceOfBefore     => f.selector == sig:deposit(uint256,address).selector ||
                                                    f.selector == sig:deposit(uint256,address,uint16).selector ||
                                                    f.selector == sig:mint(uint256,address).selector ||
                                                    f.selector == sig:mint(uint256,address,uint16).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector ||
                                                    f.selector == sig:transfer(address,uint256).selector ||
                                                    f.selector == sig:transferFrom(address,address,uint256).selector, "Assert 3";
    assert allowanceAfter != allowanceBefore     => f.selector == sig:approve(address,uint256).selector ||
                                                    f.selector == sig:transferFrom(address,address,uint256).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector ||
                                                    f.selector == sig:permit(address,address,uint256,uint256,bytes).selector ||
                                                    f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector, "Assert 4";
    assert noncesAfter != noncesBefore           => f.selector == sig:permit(address,address,uint256,uint256,bytes).selector ||
                                                    f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector, "Assert 5";
    assert chiAfter != chiBefore                 => f.selector == sig:initialize().selector ||
                                                    f.selector == sig:cut(uint256).selector ||
                                                    f.selector == sig:drip().selector ||
                                                    f.selector == sig:deposit(uint256,address).selector ||
                                                    f.selector == sig:deposit(uint256,address,uint16).selector ||
                                                    f.selector == sig:mint(uint256,address).selector ||
                                                    f.selector == sig:mint(uint256,address,uint16).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector, "Assert 6";
    assert rhoAfter != rhoBefore                 => f.selector == sig:initialize().selector ||
                                                    f.selector == sig:cut(uint256).selector ||
                                                    f.selector == sig:drip().selector ||
                                                    f.selector == sig:deposit(uint256,address).selector ||
                                                    f.selector == sig:deposit(uint256,address,uint16).selector ||
                                                    f.selector == sig:mint(uint256,address).selector ||
                                                    f.selector == sig:mint(uint256,address,uint16).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector, "Assert 7";
    assert syrAfter != syrBefore                 => f.selector == sig:initialize().selector ||
                                                    f.selector == sig:file(bytes32,uint256).selector, "Assert 8";
    assert capAfter != capBefore                 => f.selector == sig:file(bytes32,uint256).selector, "Assert 9";
}

// Verify correct storage changes for non reverting rely
rule rely(address usr) { 
    env e;

    address other;
    require other != usr;

    mathint wardsOtherBefore = wards(other);

    rely(e, usr);

    mathint wardsUsrAfter = wards(usr);
    mathint wardsOtherAfter = wards(other);

    assert wardsUsrAfter == 1, "Assert 1";
    assert wardsOtherAfter == wardsOtherBefore, "Assert 2";
}

// Verify revert rules on rely
rule rely_revert(address usr) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    rely@withrevert(e, usr);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting deny
rule deny(address usr) {
    env e;

    address other;
    require other != usr;

    mathint wardsOtherBefore = wards(other);

    deny(e, usr);

    mathint wardsUsrAfter = wards(usr);
    mathint wardsOtherAfter = wards(other);

    assert wardsUsrAfter == 0, "Assert 1";
    assert wardsOtherAfter == wardsOtherBefore, "Assert 2";
}

// Verify revert rules on deny
rule deny_revert(address usr) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    deny@withrevert(e, usr);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting file
rule file(bytes32 what, uint256 data) {
    env e;

    uint256 syrBefore = syr();
    uint256 capBefore = cap();

    file(e, what, data);

    uint256 syrAfter = syr();
    uint256 capAfter = cap();

    assert what == to_bytes32(0x7379720000000000000000000000000000000000000000000000000000000000) => syrAfter == data, "Assert 1";
    assert what != to_bytes32(0x7379720000000000000000000000000000000000000000000000000000000000) => syrAfter == syrBefore, "Assert 2";
    assert what == to_bytes32(0x6361700000000000000000000000000000000000000000000000000000000000) => capAfter == data, "Assert 3";
    assert what != to_bytes32(0x6361700000000000000000000000000000000000000000000000000000000000) => capAfter == capBefore, "Assert 4";
}

// Verify revert rules on file
rule file_revert(bytes32 what, uint256 data) {
    env e;

    mathint wardsSender = wards(e.msg.sender);
    mathint rho = rho();

    file@withrevert(e, what, data);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;
    bool revert3 = what != to_bytes32(0x7379720000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x6361700000000000000000000000000000000000000000000000000000000000);
    bool revert4 = what == to_bytes32(0x7379720000000000000000000000000000000000000000000000000000000000) &&
                   data < RAY();
    bool revert5 = what == to_bytes32(0x7379720000000000000000000000000000000000000000000000000000000000) &&
                   rho != e.block.timestamp;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5, "Revert rules failed";
}

// Verify correct storage changes for non reverting cut
rule cut(uint256 rad) {
    env e;

    mathint assets = _divup(rad, RAY());

    bytes32 ilk = ilk();
    mathint cap = cap();
    address vow = vow();

    mathint chiBefore = chi();

    uint256 totalSupply = totalSupply();
    mathint totalAssetsBefore = totalAssets(e);
    mathint usdsTotalSupplyBefore = usds.totalSupply();
    mathint usdsBalanceOfYusdsBefore = usds.balanceOf(currentContract);
    mathint vatDaiVowBefore = vat.dai(vow);

    // Correct vow set
    require vow != currentContract && vow != usdsJoin;
    // ERC20 correct behaviour
    require usdsTotalSupplyBefore >= usdsBalanceOfYusdsBefore;

    mathint chiDripCalc = defNewChi(e);
    mathint newChiCalc = totalAssetsBefore > 0 ? chiDripCalc * _subcap(totalAssetsBefore, assets) / totalAssetsBefore : 0;
    mathint lineCalc = _min(cap, _subcap(totalSupply * newChiCalc, Due));

    mathint dripDiff = totalSupply * chiDripCalc / RAY() - totalSupply * chiBefore / RAY();

    cut(e, rad);

    mathint chiAfter = chi();
    mathint totalAssetsAfter = totalAssets(e);
    mathint lineAfter; mathint a;
    a, a, a, lineAfter, a = vat.ilks(ilk);
    mathint usdsTotalSupplyAfter = usds.totalSupply();
    mathint usdsBalanceOfYusdsAfter = usds.balanceOf(currentContract);
    mathint vatDaiVowAfter = vat.dai(vow);

    assert chiAfter == newChiCalc, "Assert 1";
    assert totalAssetsAfter == totalSupply * newChiCalc / RAY(), "Assert 2";
    assert lineAfter == lineCalc, "Assert 3";
    assert usdsTotalSupplyAfter == usdsTotalSupplyBefore + dripDiff - assets, "Assert 4";
    assert usdsBalanceOfYusdsAfter == usdsBalanceOfYusdsBefore + dripDiff - assets, "Assert 5";
    assert vatDaiVowAfter == vatDaiVowBefore + assets * RAY(), "Assert 6";
}

// Verify revert rules on cut
rule cut_revert(uint256 rad) {
    env e;

    mathint assets = _divup(rad, RAY());

    mathint wardsSender = wards(e.msg.sender);

    address vow = vow();

    uint256 syr = syr();
    mathint rho = rho();
    mathint chi = chi();

    mathint totalSupply = totalSupply();
    mathint totalAssets = totalAssets(e);

    mathint usdsTotalSupply = usds.totalSupply();
    mathint usdsBalanceOfYusds = usds.balanceOf(currentContract);

    // Blockchain behaviour
    require e.block.timestamp >= rho();
    require e.block.timestamp < 2^64;

    mathint rpowRes = aux.rpow(syr, assert_uint256(e.block.timestamp - rho));
    mathint chiDripCalc = defNewChi(e);
    mathint newChiCalc = totalAssets > 0 ? chiDripCalc * _subcap(totalAssets, assets) / totalAssets : 0;

    mathint dripDiff = totalSupply * chiDripCalc / RAY() - totalSupply * chi / RAY();

    // Happening in initialize
    require vat.can(currentContract, usdsJoin) == 1;
    require usds.allowance(currentContract, usdsJoin) == max_uint256;
    // Happening in init scripts
    require vat.wards(currentContract) == 1;
    // Vat is functional
    require vat.live() == 1;
    // ERC20 correct behaviour
    require usdsTotalSupply >= usdsBalanceOfYusds;
    // TODO: see if can be replaced with an invariant rule
    require usdsBalanceOfYusds >= totalSupply * chi;
    // Correct behaviour usdsJoin
    require vat.dai(usdsJoin) >= usdsTotalSupply * RAY();
    // Convenience assumptions
    require usdsTotalSupply + dripDiff <= max_uint256;
    require vat.dai(currentContract) + dripDiff * RAY() <= max_uint256;
    require vat.dai(vow) + assets * RAY() <= max_uint256;
    require vat.sin(vow) + dripDiff * RAY() <= max_uint256;
    require vat.vice() + dripDiff * RAY() <= max_uint256;
    require vat.debt() + dripDiff * RAY() <= max_uint256;
    require vat.dai(usdsJoin) + dripDiff * RAY() <= max_uint256;
    require assets * RAY() <= max_uint256;

    cut@withrevert(e, rad);

    bool revert1  = e.msg.value > 0;
    bool revert2  = wardsSender != 1;
    bool revert3  = e.block.timestamp > rho && rpowRes * chi > max_uint256;
    bool revert4  = e.block.timestamp > rho && dripDiff < 0;
    bool revert5  = e.block.timestamp > rho && totalSupply * chiDripCalc > max_uint256;
    bool revert6  = e.block.timestamp > rho && totalSupply * chi > max_uint256;
    bool revert7  = e.block.timestamp > rho && dripDiff * RAY() > max_uint256;
    bool revert8  = chiDripCalc * _subcap(totalAssets, assets) > max_uint256;
    bool revert9  = totalAssets == 0;
    bool revert10 = assets > usdsBalanceOfYusds + dripDiff;
    bool revert11 = totalSupply * newChiCalc > max_uint256;

    assert lastReverted <=> revert1  || revert2 || revert3 ||
                            revert4  || revert5 || revert6 ||
                            revert7  || revert8 || revert9 ||
                            revert10 || revert11, "Revert rules failed";
}

// Verify correct storage changes for non reverting drip
rule drip() {
    env e;

    bytes32 ilk = ilk();
    mathint cap = cap();
    address vow = vow();

    mathint chiBefore = chi();

    uint256 totalSupply = totalSupply();
    mathint totalAssetsBefore = totalAssets(e);
    mathint usdsTotalSupplyBefore = usds.totalSupply();
    mathint usdsBalanceOfYusdsBefore = usds.balanceOf(currentContract);

    // Correct vow set
    require vow != currentContract && vow != usdsJoin;
    // ERC20 correct behaviour
    require usdsTotalSupplyBefore >= usdsBalanceOfYusdsBefore;

    mathint newChiCalc = defNewChi(e);
    mathint lineCalc = _min(cap, _subcap(totalSupply * newChiCalc, Due));

    mathint dripDiff = totalSupply * newChiCalc / RAY() - totalSupply * chiBefore / RAY();

    drip(e);

    mathint chiAfter = chi();
    mathint totalAssetsAfter = totalAssets(e);
    mathint lineAfter; mathint a;
    a, a, a, lineAfter, a = vat.ilks(ilk);
    mathint usdsTotalSupplyAfter = usds.totalSupply();
    mathint usdsBalanceOfYusdsAfter = usds.balanceOf(currentContract);

    assert chiAfter == newChiCalc, "Assert 1";
    assert totalAssetsAfter == totalSupply * newChiCalc / RAY(), "Assert 2";
    assert lineAfter == lineCalc, "Assert 3";
    assert usdsTotalSupplyAfter == usdsTotalSupplyBefore + dripDiff, "Assert 4";
    assert usdsBalanceOfYusdsAfter == usdsBalanceOfYusdsBefore + dripDiff, "Assert 5";
}

// Verify revert rules on drip
rule drip_revert() {
    env e;

    address vow = vow();

    uint256 syr = syr();
    mathint rho = rho();
    mathint chi = chi();

    mathint totalSupply = totalSupply();
    mathint totalAssets = totalAssets(e);

    mathint usdsTotalSupply = usds.totalSupply();
    mathint usdsBalanceOfYusds = usds.balanceOf(currentContract);

    // Blockchain behaviour
    require e.block.timestamp >= rho();
    require e.block.timestamp < 2^64;

    mathint rpowRes = aux.rpow(syr, assert_uint256(e.block.timestamp - rho));
    mathint newChiCalc = defNewChi(e);

    mathint dripDiff = totalSupply * newChiCalc / RAY() - totalSupply * chi / RAY();

    // Happening in initialize
    require vat.can(currentContract, usdsJoin) == 1;
    require usds.allowance(currentContract, usdsJoin) == max_uint256;
    // Happening in init scripts
    require vat.wards(currentContract) == 1;
    // Vat is functional
    require vat.live() == 1;
    // ERC20 correct behaviour
    require usdsTotalSupply >= usdsBalanceOfYusds;
    // TODO: see if can be replaced with an invariant rule
    require usdsBalanceOfYusds >= totalSupply * chi;
    // Correct behaviour usdsJoin
    require vat.dai(usdsJoin) >= usdsTotalSupply * RAY();
    // Convenience assumptions
    require usdsTotalSupply + dripDiff <= max_uint256;
    require vat.dai(currentContract) + dripDiff * RAY() <= max_uint256;
    require vat.sin(vow) + dripDiff * RAY() <= max_uint256;
    require vat.vice() + dripDiff * RAY() <= max_uint256;
    require vat.debt() + dripDiff * RAY() <= max_uint256;
    require vat.dai(usdsJoin) + dripDiff * RAY() <= max_uint256;

    drip@withrevert(e);

    bool revert1 = e.msg.value > 0;
    bool revert2 = e.block.timestamp > rho && rpowRes * chi > max_uint256;
    bool revert3 = e.block.timestamp > rho && dripDiff < 0;
    bool revert4 = e.block.timestamp > rho && totalSupply * newChiCalc > max_uint256;
    bool revert5 = e.block.timestamp > rho && totalSupply * chi > max_uint256;
    bool revert6 = e.block.timestamp > rho && dripDiff * RAY() > max_uint256;
    bool revert7 = totalSupply * newChiCalc > max_uint256;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7, "Revert rules failed";
}

// Verify correct storage changes for non reverting transfer
rule transfer(address to, uint256 value) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    address other;
    require other != e.msg.sender && other != to;

    mathint balanceOfSenderBefore = balanceOf(e.msg.sender);
    mathint balanceOfToBefore = balanceOf(to);
    mathint balanceOfOtherBefore = balanceOf(other);

    transfer(e, to, value);

    mathint balanceOfSenderAfter = balanceOf(e.msg.sender);
    mathint balanceOfToAfter = balanceOf(to);
    mathint balanceOfOtherAfter = balanceOf(other);

    assert e.msg.sender != to => balanceOfSenderAfter == balanceOfSenderBefore - value, "Assert 1";
    assert e.msg.sender != to => balanceOfToAfter == balanceOfToBefore + value, "Assert 2";
    assert e.msg.sender == to => balanceOfSenderAfter == balanceOfSenderBefore, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
}

// Verify revert rules on transfer
rule transfer_revert(address to, uint256 value) {
    env e;

    mathint balanceOfSender = balanceOf(e.msg.sender);

    transfer@withrevert(e, to, value);

    bool revert1 = e.msg.value > 0;
    bool revert2 = to == 0 || to == currentContract;
    bool revert3 = balanceOfSender < to_mathint(value);

    assert lastReverted <=> revert1 || revert2 || revert3, "Revert rules failed";
}

// Verify correct storage changes for non reverting transferFrom
rule transferFrom(address from, address to, uint256 value) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    address other;
    require other != from && other != to;
    address other2; address other3;
    require other2 != from || other3 != e.msg.sender;

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfFromBefore = balanceOf(from);
    mathint balanceOfToBefore = balanceOf(to);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint allowanceFromSenderBefore = allowance(from, e.msg.sender);
    mathint allowanceOtherBefore = allowance(other2, other3);

    transferFrom(e, from, to, value);

    mathint balanceOfFromAfter = balanceOf(from);
    mathint balanceOfToAfter = balanceOf(to);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint allowanceFromSenderAfter = allowance(from, e.msg.sender);
    mathint allowanceOtherAfter = allowance(other2, other3);

    assert from != to => balanceOfFromAfter == balanceOfFromBefore - value, "Assert 1";
    assert from != to => balanceOfToAfter == balanceOfToBefore + value, "Assert 2";
    assert from == to => balanceOfFromAfter == balanceOfFromBefore, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert e.msg.sender != from && allowanceFromSenderBefore != max_uint256 => allowanceFromSenderAfter == allowanceFromSenderBefore - value, "Assert 5";
    assert e.msg.sender == from => allowanceFromSenderAfter == allowanceFromSenderBefore, "Assert 6";
    assert allowanceFromSenderBefore == max_uint256 => allowanceFromSenderAfter == allowanceFromSenderBefore, "Assert 7";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 8";
}

// Verify revert rules on transferFrom
rule transferFrom_revert(address from, address to, uint256 value) {
    env e;

    mathint balanceOfFrom = balanceOf(from);
    mathint allowanceFromSender = allowance(from, e.msg.sender);

    transferFrom@withrevert(e, from, to, value);

    bool revert1 = e.msg.value > 0;
    bool revert2 = to == 0 || to == currentContract;
    bool revert3 = balanceOfFrom < to_mathint(value);
    bool revert4 = allowanceFromSender < to_mathint(value) && e.msg.sender != from;

    assert lastReverted <=> revert1 || revert2 || revert3 || revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting approve
rule approve(address spender, uint256 value) {
    env e;

    address anyUsr; address anyUsr2;
    require anyUsr != e.msg.sender || anyUsr2 != spender;

    mathint allowanceOtherBefore = allowance(anyUsr, anyUsr2);

    approve(e, spender, value);

    mathint allowanceSenderSpenderAfter = allowance(e.msg.sender, spender);
    mathint allowanceOtherAfter = allowance(anyUsr, anyUsr2);

    assert allowanceSenderSpenderAfter == to_mathint(value), "Assert 1";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 2";
}

// Verify revert rules on approve
rule approve_revert(address spender, uint256 value) {
    env e;

    approve@withrevert(e, spender, value);

    bool revert1 = e.msg.value > 0;

    assert lastReverted <=> revert1, "Revert rules failed";
}

// Verify correct behaviour of asset getter
rule asset() {
    env e;

    address asset = asset(e);

    assert asset == usds(), "Assert 1";
}

// Verify correct behaviour of totalAssets getter
rule totalAssets() {
    env e;

    mathint totalAssetsCalc = defConvertToAssets(e, totalSupply());

    mathint totalAssets = totalAssets(e);

    assert totalAssets == totalAssetsCalc, "Assert 1";
}

// Verify correct behaviour of convertToShares getter
rule convertToShares(uint256 assets) {
    env e;

    mathint sharesCalc = defConvertToShares(e, assets);

    mathint shares = convertToShares(e, assets);

    assert shares == sharesCalc, "Assert 1";
}

// Verify correct behaviour of convertToAssets getter
rule convertToAssets(uint256 shares) {
    env e;

    mathint assetsCalc = defConvertToAssets(e, shares);

    mathint assets = convertToAssets(e, shares);

    assert assets == assetsCalc, "Assert 1";
}

// Verify correct behaviour of maxDeposit getter
rule maxDeposit(address anyAddr) {
    env e;

    mathint assets = maxDeposit(e, anyAddr);

    assert assets == max_uint256, "Assert 1";
}

// Verify correct behaviour of previewDeposit getter
rule previewDeposit(uint256 assets) {
    env e;

    mathint sharesCalc = defConvertToShares(e, assets);

    mathint shares = previewDeposit(e, assets);

    assert shares == sharesCalc, "Assert 1";
}

// Verify correct storage changes for non reverting deposit
rule deposit(uint256 assets, address receiver, uint16 referral) {
    env e;

    require e.msg.sender != currentContract;

    address other;
    require other != receiver;

    bytes32 ilk = ilk();

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdsBalanceOfYUsdsBefore = usds.balanceOf(currentContract);
    mathint usdsBalanceOfSenderBefore = usds.balanceOf(e.msg.sender);

    mathint cap = cap();
    mathint newChiCalc = defNewChi(e);
    mathint sharesCalc = defConvertToShares(e, assets);
    mathint lineCalc = _min(cap, _subcap((totalSupplyBefore + sharesCalc) * newChiCalc, Due));

    mathint dripDiffCalc = totalSupplyBefore * newChiCalc / RAY() - totalSupplyBefore * chi() / RAY();

    // ERC20 correct behaviour
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;
    require usds.totalSupply() >= usdsBalanceOfYUsdsBefore + usdsBalanceOfSenderBefore;

    bool passReferral;
    mathint shares = passReferral ? deposit(e, assets, receiver, referral) : deposit(e, assets, receiver);

    mathint chiAfter = chi();
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdsBalanceOfYUsdsAfter = usds.balanceOf(currentContract);
    mathint usdsBalanceOfSenderAfter = usds.balanceOf(e.msg.sender);
    mathint lineAfter; mathint a;
    a, a, a, lineAfter, a = vat.ilks(ilk);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdsBalanceOfYUsdsAfter == usdsBalanceOfYUsdsBefore + assets + dripDiffCalc, "Assert 5";
    assert usdsBalanceOfSenderAfter == usdsBalanceOfSenderBefore - assets, "Assert 6";
    assert chiAfter == newChiCalc, "Assert 7";
    assert lineAfter == lineCalc, "Assert 8";
}

// Verify revert rules on deposit
rule deposit_revert(uint256 assets, address receiver, uint16 referral) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    address vow = vow();

    uint256 syr = syr();
    mathint rho = rho();
    mathint chi = chi();

    // Blockchain behaviour
    require e.block.timestamp >= rho();

    mathint rpowRes = aux.rpow(syr, assert_uint256(e.block.timestamp - rho));
    mathint newChiCalc = defNewChi(e);
    mathint sharesCalc = defConvertToShares(e, assets);

    mathint totalSupply = totalSupply();

    mathint dripDiff = totalSupply * newChiCalc / RAY() - totalSupply * chi / RAY();

    // Happening in initialize
    require vat.can(currentContract, usdsJoin) == 1;
    // Happening in init scripts
    require vat.wards(currentContract) == 1;
    // Vat is functional
    require vat.live() == 1;
    // ERC20 correct behaviour
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(e.msg.sender);
    // Convenience assumptions
    require usds.totalSupply() + dripDiff <= max_uint256;
    require vat.dai(currentContract) + dripDiff * RAY() <= max_uint256;
    require vat.sin(vow) + dripDiff * RAY() <= max_uint256;
    require vat.vice() + dripDiff * RAY() <= max_uint256;
    require vat.debt() + dripDiff * RAY() <= max_uint256;
    require vat.dai(usdsJoin) + dripDiff * RAY() <= max_uint256;
    // Sender assumptions
    require usds.allowance(e.msg.sender, currentContract) >= assets;
    require usds.balanceOf(e.msg.sender) >= assets;

    bool passReferral;
    if (passReferral) {
        deposit@withrevert(e, assets, receiver, referral);
    } else {
        deposit@withrevert(e, assets, receiver);
    }

    bool revert1  = e.msg.value > 0;
    bool revert2  = assets * RAY() > max_uint256;
    bool revert3  = e.block.timestamp == rho && chi == 0 || e.block.timestamp > rho && newChiCalc == 0;
    bool revert4  = e.block.timestamp > rho && rpowRes * chi > max_uint256;
    bool revert5  = e.block.timestamp > rho && dripDiff < 0;
    bool revert6  = e.block.timestamp > rho && totalSupply * newChiCalc > max_uint256;
    bool revert7  = e.block.timestamp > rho && totalSupply * chi > max_uint256;
    bool revert8  = e.block.timestamp > rho && dripDiff * RAY() > max_uint256;
    bool revert9  = receiver == 0 || receiver == currentContract;
    bool revert10 = (totalSupply + sharesCalc) * newChiCalc > max_uint256;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7 || revert8 || revert9 ||
                            revert10, "Revert rules failed";
}

// Verify correct behaviour of maxMint getter
rule maxMint(address anyAddr) {
    env e;

    mathint shares = maxMint(e, anyAddr);

    assert shares == max_uint256, "Assert 1";
}

// Verify correct behaviour of previewMint getter
rule previewMint(uint256 shares) {
    env e;

    mathint newChiCalc = defNewChi(e);
    mathint assetsCalc = _divup(shares * newChiCalc, RAY());

    mathint assets = previewMint(e, shares);

    assert assets == assetsCalc, "Assert 1";
}

// Verify correct storage changes for non reverting mint
rule mint(uint256 shares, address receiver, uint16 referral) {
    env e;

    require e.msg.sender != currentContract;

    address other;
    require other != receiver;

    bytes32 ilk = ilk();

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdsBalanceOfYUsdsBefore = usds.balanceOf(currentContract);
    mathint usdsBalanceOfSenderBefore = usds.balanceOf(e.msg.sender);

    mathint cap = cap();
    mathint newChiCalc = defNewChi(e);
    mathint assetsCalc = _divup(shares * newChiCalc, RAY());
    mathint lineCalc = _min(cap, _subcap((totalSupplyBefore + shares) * newChiCalc, Due));

    mathint dripDiffCalc = totalSupplyBefore * newChiCalc / RAY() - totalSupplyBefore * chi() / RAY();

    // ERC20 correct behaviour
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;
    require usds.totalSupply() >= usdsBalanceOfYUsdsBefore + usdsBalanceOfSenderBefore;

    bool passReferral;
    mathint assets = passReferral ? mint(e, shares, receiver, referral) : mint(e, shares, receiver);

    mathint chiAfter = chi();
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdsBalanceOfYUsdsAfter = usds.balanceOf(currentContract);
    mathint usdsBalanceOfSenderAfter = usds.balanceOf(e.msg.sender);
    mathint lineAfter; mathint a;
    a, a, a, lineAfter, a = vat.ilks(ilk);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdsBalanceOfYUsdsAfter == usdsBalanceOfYUsdsBefore + assets + dripDiffCalc, "Assert 5";
    assert usdsBalanceOfSenderAfter == usdsBalanceOfSenderBefore - assets, "Assert 6";
    assert chiAfter == newChiCalc, "Assert 7";
    assert lineAfter == lineCalc, "Assert 8";
}

// Verify revert rules on mint
rule mint_revert(uint256 shares, address receiver, uint16 referral) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    address vow = vow();

    uint256 syr = syr();
    mathint rho = rho();
    mathint chi = chi();

    // Blockchain behaviour
    require e.block.timestamp >= rho();

    mathint rpowRes = aux.rpow(syr, assert_uint256(e.block.timestamp - rho));
    mathint newChiCalc = defNewChi(e);
    mathint assetsCalc = _divup(shares * newChiCalc, RAY());

    mathint totalSupply = totalSupply();

    mathint dripDiff = totalSupply * newChiCalc / RAY() - totalSupply * chi / RAY();

    // Happening in initialize
    require vat.can(currentContract, usdsJoin) == 1;
    // Happening in init scripts
    require vat.wards(currentContract) == 1;
    // Vat is functional
    require vat.live() == 1;
    // ERC20 correct behaviour
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(e.msg.sender);
    // Convenience assumptions
    require usds.totalSupply() + dripDiff <= max_uint256;
    require vat.dai(currentContract) + dripDiff * RAY() <= max_uint256;
    require vat.sin(vow) + dripDiff * RAY() <= max_uint256;
    require vat.vice() + dripDiff * RAY() <= max_uint256;
    require vat.debt() + dripDiff * RAY() <= max_uint256;
    require vat.dai(usdsJoin) + dripDiff * RAY() <= max_uint256;
    // Sender assumptions
    require usds.allowance(e.msg.sender, currentContract) >= assetsCalc;
    require usds.balanceOf(e.msg.sender) >= assetsCalc;

    bool passReferral;
    if (passReferral) {
        mint@withrevert(e, shares, receiver, referral);
    } else {
        mint@withrevert(e, shares, receiver);
    }

    bool revert1  = e.msg.value > 0;
    bool revert2  = shares * newChiCalc > max_uint256;
    bool revert3  = e.block.timestamp > rho && rpowRes * chi > max_uint256;
    bool revert4  = e.block.timestamp > rho && dripDiff < 0;
    bool revert5  = e.block.timestamp > rho && totalSupply * newChiCalc > max_uint256;
    bool revert6  = e.block.timestamp > rho && totalSupply * chi > max_uint256;
    bool revert7  = e.block.timestamp > rho && dripDiff * RAY() > max_uint256;
    bool revert8  = receiver == 0 || receiver == currentContract;
    bool revert9  = totalSupply + shares > max_uint256;
    bool revert10 = (totalSupply + shares) * newChiCalc > max_uint256;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7 || revert8 || revert9 ||
                            revert10, "Revert rules failed";
}

// Verify correct behaviour of maxWithdraw getter
rule maxWithdraw(address owner) {
    env e;

    bytes32 ilk = ilk();

    // Blockchain behaviour
    require e.block.timestamp >= rho();
    uint256 jugDuty; mathint jugRho;
    jugDuty, jugRho = jug.ilks(ilk);
    require e.block.timestamp >= jugRho;

    mathint newChiCalc = defNewChi(e);

    mathint vatIlkArt; mathint vatIlkRatePrev; mathint a;
    vatIlkArt, vatIlkRatePrev, a, a, a = vat.ilks(ilk);

    mathint jugRpowRes = aux.rpow(jugDuty, require_uint256(e.block.timestamp - jugRho));
    mathint vatIlkRate = e.block.timestamp > jugRho ? jugRpowRes * vatIlkRatePrev / RAY() : vatIlkRatePrev;

    mathint assetsCalc = _min(
        defConvertToAssets(e, balanceOf(owner)),
        _subcap(totalSupply() * newChiCalc, vatIlkArt * vatIlkRate + Due) / RAY()
    );

    mathint assets = maxWithdraw(e, owner);

    assert assetsCalc == assets, "Assert 1";
}

// Verify correct behaviour of previewWithdraw getter
rule previewWithdraw(uint256 assets) {
    env e;

    mathint newChiCalc = defNewChi(e);
    mathint sharesCalc = newChiCalc > 0 ? _divup(assets * RAY(), newChiCalc) : 0; // Else path won't be evaluated as should revert

    mathint shares = previewWithdraw(e, assets);

    assert shares == sharesCalc, "Assert 1";
}

// Verify correct storage changes for non reverting withdraw
rule withdraw(uint256 assets, address receiver, address owner) {
    env e;

    address other;
    require other != owner;

    bytes32 ilk = ilk();

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdsBalanceOfYUsdsBefore = usds.balanceOf(currentContract);
    mathint usdsBalanceOfReceiverBefore = usds.balanceOf(receiver);

    mathint cap = cap();
    mathint newChiCalc = defNewChi(e);
    mathint sharesCalc = newChiCalc > 0 ? _divup(assets * RAY(), newChiCalc) : 0; // Else path won't be evaluated as should revert
    mathint lineCalc = _min(cap, _subcap((totalSupplyBefore - sharesCalc) * newChiCalc, Due));

    mathint dripDiffCalc = totalSupplyBefore * newChiCalc / RAY() - totalSupplyBefore * chi() / RAY();

    // ERC20 correct behaviour
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;
    require usds.totalSupply() >= usdsBalanceOfYUsdsBefore + usdsBalanceOfReceiverBefore;

    mathint shares = withdraw(e, assets, receiver, owner);

    mathint chiAfter = chi();
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdsBalanceOfYUsdsAfter = usds.balanceOf(currentContract);
    mathint usdsBalanceOfReceiverAfter = usds.balanceOf(receiver);
    mathint lineAfter; mathint a;
    a, a, a, lineAfter, a = vat.ilks(ilk);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != currentContract => usdsBalanceOfReceiverAfter == usdsBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != currentContract => usdsBalanceOfYUsdsAfter == usdsBalanceOfYUsdsBefore - assets + dripDiffCalc, "Assert 6";
    assert receiver == currentContract => usdsBalanceOfReceiverAfter == usdsBalanceOfReceiverBefore + dripDiffCalc, "Assert 7";
    assert chiAfter == newChiCalc, "Assert 8";
    assert lineAfter == lineCalc, "Assert 9";
}

// Verify revert rules on withdraw
rule withdraw_revert(uint256 assets, address receiver, address owner) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    bytes32 ilk = ilk();
    address vow = vow();

    mathint totalSupply = totalSupply();
    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);

    uint256 syr = syr();
    mathint rho = rho();
    mathint chi = chi();

    uint256 jugDuty; mathint jugRho;
    jugDuty, jugRho = jug.ilks(ilk);

    // Blockchain behaviour
    require e.block.timestamp >= rho;
    require e.block.timestamp >= jugRho;

    mathint rpowRes = aux.rpow(syr, assert_uint256(e.block.timestamp - rho));
    mathint newChiCalc = defNewChi(e);
    mathint sharesCalc = newChiCalc > 0 ? _divup(assets * RAY(), newChiCalc) : 0;

    mathint dripDiff = totalSupply * newChiCalc / RAY() - totalSupply * chi / RAY();

    mathint vatIlkArt; mathint vatIlkRatePrev; mathint a;
    vatIlkArt, vatIlkRatePrev, a, a, a = vat.ilks(ilk);

    mathint jugRpowRes = aux.rpow(jugDuty, require_uint256(e.block.timestamp - jugRho));
    mathint vatIlkRate = e.block.timestamp > jugRho ? jugRpowRes * vatIlkRatePrev / RAY() : vatIlkRatePrev;

    // Correct vow set
    require vow != currentContract && vow != usdsJoin;
    require vow == jug.vow();
    // Happening in initialize
    require vat.can(currentContract, usdsJoin) == 1;
    // Happening in init scripts
    require vat.wards(currentContract) == 1;
    // Vat is functional
    require vat.live() == 1;
    // ERC20 correct behaviour
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(receiver);
    // TODO: see if can be replaced with an invariant rule
    require usds.balanceOf(currentContract) >= totalSupply * chi;
    // Existing set up
    require vat.wards(jug) == 1;
    // Convenience assumptions
    require usds.totalSupply() + dripDiff <= max_uint256;
    require vat.dai(currentContract) + dripDiff * RAY() <= max_uint256;
    require vat.dai(vow) + vatIlkArt * (vatIlkRate - vatIlkRatePrev) <= max_uint256;
    require vat.sin(vow) + dripDiff * RAY() <= max_uint256;
    require vat.vice() + dripDiff * RAY() <= max_uint256;
    require vat.debt() + dripDiff * RAY() + vatIlkArt * (vatIlkRate - vatIlkRatePrev) <= max_uint256;
    require vat.dai(usdsJoin) + dripDiff * RAY() <= max_uint256;
    require jug.base() == 0;
    require jugDuty >= RAY();
    require jugRpowRes * vatIlkRatePrev <= max_uint256;
    require vatIlkArt <= max_int256();
    require vatIlkRatePrev <= max_int256();
    require vatIlkRate <= max_int256();
    require vatIlkArt * (vatIlkRate - vatIlkRatePrev) <= max_int256();

    withdraw@withrevert(e, assets, receiver, owner);

    bool revert1  = e.msg.value > 0;
    bool revert2  = assets * RAY() > max_uint256;
    bool revert3  = assets > 0 && (e.block.timestamp == rho && chi == 0 || e.block.timestamp > rho && newChiCalc == 0);
    bool revert4  = e.block.timestamp > rho && rpowRes * chi > max_uint256;
    bool revert5  = e.block.timestamp > rho && dripDiff < 0;
    bool revert6  = e.block.timestamp > rho && totalSupply * newChiCalc > max_uint256;
    bool revert7  = e.block.timestamp > rho && totalSupply * chi > max_uint256;
    bool revert8  = e.block.timestamp > rho && dripDiff * RAY() > max_uint256;
    bool revert9  = balanceOfOwner < sharesCalc;
    bool revert10 = owner != e.msg.sender && allowanceOwnerSender < sharesCalc;
    bool revert11 = vatIlkArt * vatIlkRate + Due + assets * RAY() > totalSupply * newChiCalc;

    assert lastReverted <=> revert1  || revert2  || revert3 ||
                            revert4  || revert5  || revert6 ||
                            revert7  || revert8  || revert9 ||
                            revert10 || revert11, "Revert rules failed";
}

// Verify correct behaviour of maxRedeem getter
rule maxRedeem(address owner) {
    env e;

    bytes32 ilk = ilk();

    // Blockchain behaviour
    require e.block.timestamp >= rho();
    uint256 jugDuty; mathint jugRho;
    jugDuty, jugRho = jug.ilks(ilk);
    require e.block.timestamp >= jugRho;

    mathint newChiCalc = defNewChi(e);

    mathint vatIlkArt; mathint vatIlkRatePrev; mathint a;
    vatIlkArt, vatIlkRatePrev, a, a, a = vat.ilks(ilk);

    mathint jugRpowRes = aux.rpow(jugDuty, require_uint256(e.block.timestamp - jugRho));
    mathint vatIlkRate = e.block.timestamp > jugRho ? jugRpowRes * vatIlkRatePrev / RAY() : vatIlkRatePrev;

    mathint sharesCalc = _min(
        balanceOf(owner),
        newChiCalc > 0 ? _subcap(totalSupply() * newChiCalc, vatIlkArt * vatIlkRate + Due) / newChiCalc : 0 // Else path should provoke revert
    );

    mathint shares = maxRedeem(e, owner);

    assert sharesCalc == shares, "Assert 1";
}

// Verify correct behaviour of previewRedeem getter
rule previewRedeem(uint256 shares) {
    env e;

    mathint assetsCalc = defConvertToAssets(e, shares);

    mathint assets = previewRedeem(e, shares);

    assert assets == assetsCalc, "Assert 1";
}

// Verify correct storage changes for non reverting redeem
rule redeem(uint256 shares, address receiver, address owner) {
    env e;

    address other;
    require other != owner;

    bytes32 ilk = ilk();

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdsBalanceOfYUsdsBefore = usds.balanceOf(currentContract);
    mathint usdsBalanceOfReceiverBefore = usds.balanceOf(receiver);

    mathint cap = cap();
    mathint newChiCalc = defNewChi(e);
    mathint assetsCalc = defConvertToAssets(e, shares);
    mathint lineCalc = _min(cap, _subcap((totalSupplyBefore - shares) * newChiCalc, Due));

    mathint dripDiffCalc = totalSupplyBefore * newChiCalc / RAY() - totalSupplyBefore * chi() / RAY();

    // ERC20 correct behaviour
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;
    require usds.totalSupply() >= usdsBalanceOfYUsdsBefore + usdsBalanceOfReceiverBefore;

    mathint assets = redeem(e, shares, receiver, owner);

    mathint chiAfter = chi();
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdsBalanceOfYUsdsAfter = usds.balanceOf(currentContract);
    mathint usdsBalanceOfReceiverAfter = usds.balanceOf(receiver);
    mathint lineAfter; mathint a;
    a, a, a, lineAfter, a = vat.ilks(ilk);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != currentContract => usdsBalanceOfReceiverAfter == usdsBalanceOfReceiverBefore + assetsCalc, "Assert 5";
    assert receiver != currentContract => usdsBalanceOfYUsdsAfter == usdsBalanceOfYUsdsBefore - assetsCalc + dripDiffCalc, "Assert 6";
    assert receiver == currentContract => usdsBalanceOfReceiverAfter == usdsBalanceOfReceiverBefore + dripDiffCalc, "Assert 7";
    assert chiAfter == newChiCalc, "Assert 8";
    assert lineAfter == lineCalc, "Assert 9";
}

// Verify revert rules on redeem
rule redeem_revert(uint256 shares, address receiver, address owner) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    bytes32 ilk = ilk();
    address vow = vow();
    
    uint256 jugDuty; mathint jugRho;
    jugDuty, jugRho = jug.ilks(ilk);

    mathint totalSupply = totalSupply();
    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);

    uint256 syr = syr();
    mathint rho = rho();
    mathint chi = chi();

    // Blockchain behaviour
    require e.block.timestamp >= rho();
    require e.block.timestamp >= jugRho;

    mathint rpowRes = aux.rpow(syr, assert_uint256(e.block.timestamp - rho));
    mathint newChiCalc = defNewChi(e);
    mathint assetsCalc = defConvertToAssets(e, shares);

    mathint dripDiff = totalSupply * newChiCalc / RAY() - totalSupply * chi / RAY();

    mathint vatIlkArt; mathint vatIlkRatePrev; mathint a;
    vatIlkArt, vatIlkRatePrev, a, a, a = vat.ilks(ilk);

    mathint jugRpowRes = aux.rpow(jugDuty, require_uint256(e.block.timestamp - jugRho));
    mathint vatIlkRate = e.block.timestamp > jugRho ? jugRpowRes * vatIlkRatePrev / RAY() : vatIlkRatePrev;

    // Correct vow set
    require vow != currentContract;
    require vow != usdsJoin;
    require vow == jug.vow();
    // Happening in initialize
    require vat.can(currentContract, usdsJoin) == 1;
    // Happening in init scripts
    require vat.wards(currentContract) == 1;
    // Vat is functional
    require vat.live() == 1;
    // Correct vow set
    require vow == jug.vow();
    // ERC20 correct behaviour
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(receiver);
    // TODO: see if can be replaced with an invariant rule
    require usds.balanceOf(currentContract) >= totalSupply * chi;
    // Existing set up
    require vat.wards(jug) == 1;
    // Convenience assumptions
    require usds.totalSupply() + dripDiff <= max_uint256;
    require vat.dai(currentContract) + dripDiff * RAY() <= max_uint256;
    require vat.dai(vow) + vatIlkArt * (vatIlkRate - vatIlkRatePrev) <= max_uint256;
    require vat.sin(vow) + dripDiff * RAY() <= max_uint256;
    require vat.vice() + dripDiff * RAY() <= max_uint256;
    require vat.debt() + dripDiff * RAY() + vatIlkArt * (vatIlkRate - vatIlkRatePrev) <= max_uint256;
    require vat.dai(usdsJoin) + dripDiff * RAY() <= max_uint256;
    require jug.base() == 0;
    require jugDuty >= RAY();
    require jugRpowRes * vatIlkRatePrev <= max_uint256;
    require vatIlkArt <= max_int256();
    require vatIlkRatePrev <= max_int256();
    require vatIlkRate <= max_int256();
    require vatIlkArt * (vatIlkRate - vatIlkRatePrev) <= max_int256();

    redeem@withrevert(e, shares, receiver, owner);

    bool revert1  = e.msg.value > 0;
    bool revert2  = shares * newChiCalc > max_uint256;
    bool revert3  = e.block.timestamp > rho && rpowRes * chi > max_uint256;
    bool revert4  = e.block.timestamp > rho && dripDiff < 0;
    bool revert5  = e.block.timestamp > rho && totalSupply * newChiCalc > max_uint256;
    bool revert6  = e.block.timestamp > rho && totalSupply * chi > max_uint256;
    bool revert7  = e.block.timestamp > rho && dripDiff * RAY() > max_uint256;
    bool revert8  = balanceOfOwner < shares;
    bool revert9  = owner != e.msg.sender && allowanceOwnerSender < shares;
    bool revert10 = vatIlkArt * vatIlkRate + Due + assetsCalc * RAY() > totalSupply * newChiCalc;

    assert lastReverted <=> revert1  || revert2 || revert3 ||
                            revert4  || revert5 || revert6 ||
                            revert7  || revert8 || revert9  ||
                            revert10, "Revert rules failed";
}

// Verify correct storage changes for non reverting permit
rule permitVRS(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;

    address anyUsr; address anyUsr2;
    require anyUsr != owner || anyUsr2 != spender;
    address other;
    require other != owner;

    mathint allowanceOtherBefore = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerBefore = nonces(owner);
    mathint noncesOtherBefore = nonces(other);

    permit(e, owner, spender, value, deadline, v, r, s);

    mathint allowanceOwnerSpenderAfter = allowance(owner, spender);
    mathint allowanceOtherAfter = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerAfter = nonces(owner);
    mathint noncesOtherAfter = nonces(other);

    assert allowanceOwnerSpenderAfter == to_mathint(value), "Assert 1";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 2";
    assert noncesOwnerBefore < max_uint256 => noncesOwnerAfter == noncesOwnerBefore + 1, "Assert 3";
    assert noncesOwnerBefore == max_uint256 => noncesOwnerAfter == 0, "Assert 4";
    assert noncesOtherAfter == noncesOtherBefore, "Assert 5";
}

// Verify revert rules on permit
rule permitVRS_revert(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;

    bytes32 digest = aux.computeDigestForToken(
                        DOMAIN_SEPARATOR(),
                        PERMIT_TYPEHASH(),
                        owner,
                        spender,
                        value,
                        nonces(owner),
                        deadline
                    );
    address ownerRecover = aux.call_ecrecover(digest, v, r, s);
    bytes32 returnedSig = owner == signer ? signer.isValidSignature(e, digest, aux.VRSToSignature(v, r, s)) : to_bytes32(0);

    permit@withrevert(e, owner, spender, value, deadline, v, r, s);

    bool revert1 = e.msg.value > 0;
    bool revert2 = e.block.timestamp > deadline;
    bool revert3 = owner == 0;
    bool revert4 = owner != ownerRecover && returnedSig != to_bytes32(0x1626ba7e00000000000000000000000000000000000000000000000000000000);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting permit
rule permitSignature(address owner, address spender, uint256 value, uint256 deadline, bytes signature) {
    env e;

    address anyUsr; address anyUsr2;
    require anyUsr != owner || anyUsr2 != spender;
    address other;
    require other != owner;

    mathint allowanceOtherBefore = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerBefore = nonces(owner);
    mathint noncesOtherBefore = nonces(other);

    permit(e, owner, spender, value, deadline, signature);

    mathint allowanceOwnerSpenderAfter = allowance(owner, spender);
    mathint allowanceOtherAfter = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerAfter = nonces(owner);
    mathint noncesOtherAfter = nonces(other);

    assert allowanceOwnerSpenderAfter == to_mathint(value), "Assert 1";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 2";
    assert noncesOwnerBefore < max_uint256 => noncesOwnerAfter == noncesOwnerBefore + 1, "Assert 3";
    assert noncesOwnerBefore == max_uint256 => noncesOwnerAfter == 0, "Assert 4";
    assert noncesOtherAfter == noncesOtherBefore, "Assert 5";
}

// Verify revert rules on permit
rule permitSignature_revert(address owner, address spender, uint256 value, uint256 deadline, bytes signature) {
    env e;

    bytes32 digest = aux.computeDigestForToken(
                        DOMAIN_SEPARATOR(),
                        PERMIT_TYPEHASH(),
                        owner,
                        spender,
                        value,
                        nonces(owner),
                        deadline
                    );
    uint8 v; bytes32 r; bytes32 s;
    v, r, s = aux.signatureToVRS(signature);
    address null_address = 0;
    address ownerRecover = aux.size(signature) == 65 ? aux.call_ecrecover(digest, v, r, s) : null_address;
    bytes32 returnedSig = owner == signer ? signer.isValidSignature(e, digest, signature) : to_bytes32(0);

    permit@withrevert(e, owner, spender, value, deadline, signature);

    bool revert1 = e.msg.value > 0;
    bool revert2 = e.block.timestamp > deadline;
    bool revert3 = owner == 0;
    bool revert4 = owner != ownerRecover && returnedSig != to_bytes32(0x1626ba7e00000000000000000000000000000000000000000000000000000000);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}
