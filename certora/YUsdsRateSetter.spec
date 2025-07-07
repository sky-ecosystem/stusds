// YUsdsRateSetter.spec

using YUsds as yusds;
using Jug as jug;
using ConvMock as conv;
using Vat as vat;
using UsdsJoinMock as usdsJoin;

methods {
    // storage variables
    function wards(address) external returns (uint256) envfree;
    function buds(address) external returns (uint256) envfree;
    function ysrCfg() external returns (uint16, uint16, uint16) envfree;
    function dutyCfg() external returns (uint16, uint16, uint16) envfree;
    function maxLine() external returns (uint256) envfree;
    function maxCap() external returns (uint256) envfree;
    function bad() external returns (uint8) envfree;
    function tau() external returns (uint64) envfree;
    function toc() external returns (uint128) envfree;
    // immutables
    function ilk() external returns (bytes32) envfree;
    //
    function jug.ilks(bytes32) external returns (uint256, uint256) envfree;
    function jug.wards(address) external returns (uint256) envfree;
    function yusds.wards(address) external returns (uint256) envfree;
    function yusds.rho() external returns (uint64) envfree;
    function yusds.ysr() external returns (uint256) envfree;
    function yusds.line() external returns (uint256) envfree;
    function yusds.cap() external returns (uint256) envfree;
    function conv.btor(uint256) external returns (uint256) envfree;
    function conv.rtob(uint256) external returns (uint256) envfree;
    //
    function _.Due() external => DueSummary() expect uint256;
}

ghost uint256 Due;
function DueSummary() returns uint256 {
    return Due;
}

definition RAY() returns mathint = 10^27;
definition RAD() returns mathint = 10^45;

invariant ysrMin_LessOrEqual_ysrMax() currentContract.ysrCfg.min <= currentContract.ysrCfg.max;
invariant dutyMin_LessOrEqual_dutyMax() currentContract.dutyCfg.min <= currentContract.dutyCfg.max;

// Verify no more entry points exist
rule entryPoints(method f) filtered { f -> !f.isView } {
    env e;

    calldataarg args;
    f(e, args);

    assert f.selector == sig:rely(address).selector ||
           f.selector == sig:deny(address).selector ||
           f.selector == sig:kiss(address).selector ||
           f.selector == sig:diss(address).selector ||
           f.selector == sig:file(bytes32,uint256).selector ||
           f.selector == sig:file(bytes32,bytes32,uint256).selector ||
           f.selector == sig:set(uint256,uint256,uint256,uint256).selector;
}

// Verify that each storage variable is only modified in the expected functions
rule storage_affected(method f) {
    env e;
    address anyAddr;

    mathint wardsBefore = wards(anyAddr);
    mathint budsBefore = buds(anyAddr);
    mathint ysrMinBefore; mathint ysrMaxBefore; mathint ysrStepBefore;
    ysrMinBefore, ysrMaxBefore, ysrStepBefore = ysrCfg();
    mathint dutyMinBefore; mathint dutyMaxBefore; mathint dutyStepBefore;
    dutyMinBefore, dutyMaxBefore, dutyStepBefore = dutyCfg();
    mathint maxLineBefore = maxLine();
    mathint maxCapBefore = maxCap();
    mathint badBefore = bad();
    mathint tauBefore = tau();
    mathint tocBefore = toc();

    calldataarg args;
    f(e, args);

    mathint wardsAfter = wards(anyAddr);
    mathint budsAfter = buds(anyAddr);
    mathint ysrMinAfter; mathint ysrMaxAfter; mathint ysrStepAfter;
    ysrMinAfter, ysrMaxAfter, ysrStepAfter = ysrCfg();
    mathint dutyMinAfter; mathint dutyMaxAfter; mathint dutyStepAfter;
    dutyMinAfter, dutyMaxAfter, dutyStepAfter = dutyCfg();
    mathint maxLineAfter = maxLine();
    mathint maxCapAfter = maxCap();
    mathint badAfter = bad();
    mathint tauAfter = tau();
    mathint tocAfter = toc();

    assert wardsAfter != wardsBefore => f.selector == sig:rely(address).selector || f.selector == sig:deny(address).selector, "Assert 1";
    assert budsAfter != budsBefore => f.selector == sig:kiss(address).selector || f.selector == sig:diss(address).selector, "Assert 2";
    assert ysrMinAfter != ysrMinBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 3";
    assert ysrMaxAfter != ysrMaxBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 4";
    assert ysrStepAfter != ysrStepBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 5";
    assert dutyMinAfter != dutyMinBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 6";
    assert dutyMaxAfter != dutyMaxBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 7";
    assert dutyStepAfter != dutyStepBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 8";
    assert maxLineAfter != maxLineBefore => f.selector == sig:file(bytes32, uint256).selector, "Assert 9";
    assert maxCapAfter != maxCapBefore => f.selector == sig:file(bytes32, uint256).selector, "Assert 10";
    assert badAfter != badBefore => f.selector == sig:file(bytes32, uint256).selector, "Assert 11";
    assert tauAfter != tauBefore => f.selector == sig:file(bytes32, uint256).selector, "Assert 12";
    assert tocAfter != tocBefore => f.selector == sig:file(bytes32, uint256).selector || f.selector == sig:set(uint256, uint256, uint256, uint256).selector, "Assert 13";
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

// Verify correct storage changes for non reverting kiss
rule kiss(address usr) {
    env e;

    address other;
    require other != usr;

    mathint budsOtherBefore = buds(other);

    kiss(e, usr);

    mathint budsUsrAfter = buds(usr);
    mathint budsOtherAfter = buds(other);

    assert budsUsrAfter == 1, "Assert 1";
    assert budsOtherAfter == budsOtherBefore, "Assert 2";
}

// Verify revert rules on kiss
rule kiss_revert(address usr) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;

    kiss@withrevert(e, usr);

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting diss
rule diss(address usr) {
    env e;

    address other;
    require other != usr;

    mathint budsOtherBefore = buds(other);

    diss(e, usr);

    mathint budsUsrAfter = buds(usr);
    mathint budsOtherAfter = buds(other);

    assert budsUsrAfter == 0, "Assert 1";
    assert budsOtherAfter == budsOtherBefore, "Assert 2";
}

// Verify revert rules on diss
rule diss_revert(address usr) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    diss@withrevert(e, usr);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting file
rule file(bytes32 what, uint256 data) {
    env e;

    mathint badBefore = bad();
    mathint tauBefore = tau();
    mathint tocBefore = toc();
    mathint maxLineBefore = maxLine();
    mathint maxCapBefore = maxCap();

    file(e, what, data);

    mathint badAfter = bad();
    mathint tauAfter = tau();
    mathint tocAfter = toc();
    mathint maxLineAfter = maxLine();
    mathint maxCapAfter = maxCap();

    assert what == to_bytes32(0x6261640000000000000000000000000000000000000000000000000000000000) => badAfter == to_mathint(data), "Assert 1";
    assert what != to_bytes32(0x6261640000000000000000000000000000000000000000000000000000000000) => badAfter == badBefore, "Assert 2";
    assert what == to_bytes32(0x7461750000000000000000000000000000000000000000000000000000000000) => tauAfter == to_mathint(data), "Assert 3";
    assert what != to_bytes32(0x7461750000000000000000000000000000000000000000000000000000000000) => tauAfter == tauBefore, "Assert 4";
    assert what == to_bytes32(0x746f630000000000000000000000000000000000000000000000000000000000) => tocAfter == to_mathint(data), "Assert 5";
    assert what != to_bytes32(0x746f630000000000000000000000000000000000000000000000000000000000) => tocAfter == tocBefore, "Assert 6";
    assert what == to_bytes32(0x6d61784c696e6500000000000000000000000000000000000000000000000000) => maxLineAfter == to_mathint(data), "Assert 7";
    assert what != to_bytes32(0x6d61784c696e6500000000000000000000000000000000000000000000000000) => maxLineAfter == maxLineBefore, "Assert 8";
    assert what == to_bytes32(0x6d61784361700000000000000000000000000000000000000000000000000000) => maxCapAfter == to_mathint(data), "Assert 9";
    assert what != to_bytes32(0x6d61784361700000000000000000000000000000000000000000000000000000) => maxCapAfter == maxCapBefore, "Assert 10";
}

// Verify revert rules on file
rule file_revert(bytes32 what, uint256 data) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;
    bool revert3 = what != to_bytes32(0x6261640000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x7461750000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x746f630000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x6d61784c696e6500000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x6d61784361700000000000000000000000000000000000000000000000000000);
    bool revert4 = what == to_bytes32(0x6261640000000000000000000000000000000000000000000000000000000000) && to_mathint(data) != 0 && to_mathint(data) != 1;
    bool revert5 = what == to_bytes32(0x7461750000000000000000000000000000000000000000000000000000000000) && to_mathint(data) > max_uint64;
    bool revert6 = what == to_bytes32(0x746f630000000000000000000000000000000000000000000000000000000000) && to_mathint(data) > max_uint128;
    bool revert7 = what == to_bytes32(0x6d61784c696e6500000000000000000000000000000000000000000000000000) && to_mathint(data) != 0 && to_mathint(data) < RAD();
    bool revert8 = what == to_bytes32(0x6d61784361700000000000000000000000000000000000000000000000000000) && to_mathint(data) >= RAD();

    file@withrevert(e, what, data);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7 || revert8, "Revert rules failed";
}

// Verify correct storage changes for non reverting file
rule file_id(bytes32 id, bytes32 what, uint256 data) {
    env e;

    bytes32 ilk = ilk();
    require ilk != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000);

    mathint ysrMinBefore; mathint ysrMaxBefore; mathint ysrStepBefore;
    ysrMinBefore, ysrMaxBefore, ysrStepBefore = ysrCfg();
    mathint dutyMinBefore; mathint dutyMaxBefore; mathint dutyStepBefore;
    dutyMinBefore, dutyMaxBefore, dutyStepBefore = dutyCfg();

    file(e, id, what, data);

    mathint ysrMinAfter; mathint ysrMaxAfter; mathint ysrStepAfter;
    ysrMinAfter, ysrMaxAfter, ysrStepAfter = ysrCfg();
    mathint dutyMinAfter; mathint dutyMaxAfter; mathint dutyStepAfter;
    dutyMinAfter, dutyMaxAfter, dutyStepAfter = dutyCfg();

    assert id == to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) &&
           what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) => ysrMinAfter == to_mathint(data), "Assert 1";
    assert id != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) ||
           what != to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) => ysrMinAfter == ysrMinBefore, "Assert 2";
    assert id == to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) &&
           what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) => ysrMaxAfter == to_mathint(data), "Assert 3";
    assert id != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) ||
           what != to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) => ysrMaxAfter == ysrMaxBefore, "Assert 4";
    assert id == to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) &&
           what == to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000) => ysrStepAfter == to_mathint(data), "Assert 5";
    assert id != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) ||
           what != to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000) => ysrStepAfter == ysrStepBefore, "Assert 6";
    assert id == ilk &&
           what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) => dutyMinAfter == to_mathint(data), "Assert 7";
    assert id != ilk ||
           what != to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) => dutyMinAfter == dutyMinBefore, "Assert 8";
    assert id == ilk &&
           what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) => dutyMaxAfter == to_mathint(data), "Assert 9";
    assert id != ilk ||
           what != to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) => dutyMaxAfter == dutyMaxBefore, "Assert 10";
    assert id == ilk &&
           what == to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000) => dutyStepAfter == to_mathint(data), "Assert 11";
    assert id != ilk ||
           what != to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000) => dutyStepAfter == dutyStepBefore, "Assert 12";
}

// Verify revert rules on file
rule file_id_revert(bytes32 id, bytes32 what, uint256 data) {
    env e;

    bytes32 ilk = ilk();
    require ilk != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000);

    mathint wardsSender = wards(e.msg.sender);
    mathint ysrMin; mathint ysrMax; mathint a;
    ysrMin, ysrMax, a = ysrCfg();
    mathint dutyMin; mathint dutyMax;
    dutyMin, dutyMax, a = dutyCfg();

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;
    bool revert3 = id != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) &&
                   id != ilk;
    bool revert4 = to_mathint(data) > max_uint16;
    bool revert5 = what != to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000);
    bool revert6 = id == to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) &&
                   what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) > ysrMax;
    bool revert7 = id == ilk &&
                   what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) > dutyMax;
    bool revert8 = id == to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000) &&
                   what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) < ysrMin;
    bool revert9 = id == ilk &&
                   what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) < dutyMin;

    file@withrevert(e, id, what, data);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7 || revert8 || revert9, "Revert rules failed";
}

// Verify correct storage changes for non reverting set
rule set(uint256 ysrBps, uint256 dutyBps, uint256 line, uint256 cap) {
    env e;
    bytes32 ilk = ilk();
    require ilk != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000);

    mathint rhoBefore = yusds.rho();
    mathint jRhoBefore; mathint a;
    a, jRhoBefore = jug.ilks(ilk);

    mathint ysrRAY = conv.btor(ysrBps);
    mathint dutyRAY = conv.btor(dutyBps);

    set(e, ysrBps, dutyBps, line, cap);

    mathint ysrAfter = yusds.ysr();
    mathint rhoAfter = yusds.rho();
    mathint dutyAfter; mathint jRhoAfter;
    dutyAfter, jRhoAfter = jug.ilks(ilk);
    mathint lineAfter = yusds.line();
    mathint capAfter = yusds.cap();

    assert rhoAfter == e.block.timestamp, "Assert 1";
    assert ysrAfter == ysrRAY, "Assert 2";
    assert jRhoAfter == e.block.timestamp, "Assert 3";
    assert dutyAfter == dutyRAY, "Assert 4";
    assert lineAfter == line, "Assert 5";
    assert capAfter == cap, "Assert 6";
    satisfy rhoBefore < rhoAfter, "Satisfy 1"; // Proves that yusds.drip() gets called
    satisfy jRhoBefore < jRhoAfter, "Satisfy 2"; // Proves that jug.drip(ilk) gets called
}

// Verify revert rules on set
rule set_revert(uint256 ysrBps, uint256 dutyBps, uint256 line, uint256 cap) {
    env e;

    bytes32 ilk = ilk();
    require ilk != to_bytes32(0x5953520000000000000000000000000000000000000000000000000000000000);

    mathint budsSender = buds(e.msg.sender);
    mathint bad = bad();
    mathint maxLine = maxLine();
    mathint maxCap = maxCap();
    mathint tau = tau();
    mathint toc = toc();
    mathint ysrMin; mathint ysrMax; mathint ysrStep;
    ysrMin, ysrMax, ysrStep = ysrCfg();
    mathint dutyMin; mathint dutyMax; mathint dutyStep;
    dutyMin, dutyMax, dutyStep = dutyCfg();

    mathint rho = yusds.rho();
    uint256 ysr = yusds.ysr();
    uint256 duty; mathint jRho;
    duty, jRho = jug.ilks(ilk);

    mathint ysrOldBps = conv.rtob(ysr) < ysrMin ? ysrMin : (conv.rtob(ysr) > ysrMax ? ysrMax : conv.rtob(ysr));
    mathint dutyOldBps = conv.rtob(duty) < dutyMin ? dutyMin : (conv.rtob(duty) > dutyMax ? dutyMax : conv.rtob(duty));
    mathint dutyDelta = dutyBps > dutyOldBps ? dutyBps - dutyOldBps : dutyOldBps - dutyBps;
    mathint ysrDelta = ysrBps > ysrOldBps ? ysrBps - ysrOldBps : ysrOldBps - ysrBps;

    mathint ysrRAY = conv.btor(ysrBps);
    mathint dutyRAY = conv.btor(dutyBps);

    requireInvariant ysrMin_LessOrEqual_ysrMax;
    requireInvariant dutyMin_LessOrEqual_dutyMax;

    // Happening in init scripts
    require yusds.wards(currentContract) == 1;
    require jug.wards(currentContract) == 1;
    // Contracts behaviour
    require rho <= e.block.timestamp && jRho <= e.block.timestamp;
    // Practical assumption
    require e.block.timestamp <= max_uint64;

    bool revert1  = e.msg.value > 0;
    bool revert2  = bad > 0;
    bool revert3  = budsSender != 1;
    bool revert4  = tau + toc > max_uint128;
    bool revert5  = e.block.timestamp < tau + toc;
    bool revert6  = ysrStep == 0;
    bool revert7  = ysrBps < ysrMin;
    bool revert8  = ysrBps > ysrMax;
    bool revert9  = ysrDelta > ysrStep;
    bool revert10 = ysrRAY < RAY(); // This actually doesn't trigger as conv used won't return that value
    bool revert11 = dutyStep == 0;
    bool revert12 = dutyBps < dutyMin;
    bool revert13 = dutyBps > dutyMax;
    bool revert14 = dutyDelta > dutyStep;
    bool revert15 = dutyRAY < RAY();
    bool revert16 = line > maxLine;
    bool revert17 = cap > maxCap;

    storage initial = lastStorage;

    // Filter out all the reverts happening in both drip calls
    yusds.drip(e);
    jug.drip(e, ilk);
    
    set@withrevert(e, ysrBps, dutyBps, line, cap) at initial;

    assert lastReverted <=> revert1  || revert2  || revert3  ||
                            revert4  || revert5  || revert6  ||
                            revert7  || revert8  || revert9  ||
                            revert10 || revert11 || revert12 ||
                            revert13 || revert14 || revert15 ||
                            revert16 || revert17 , "Revert rules failed";
}
