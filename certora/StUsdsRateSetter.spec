// StUsdsRateSetter.spec

using StUsds as stusds;
using Jug as jug;
using ConvMock as conv;
using Vat as vat;
using UsdsJoinMock as usdsJoin;

methods {
    // storage variables
    function wards(address) external returns (uint256) envfree;
    function buds(address) external returns (uint256) envfree;
    function strCfg() external returns (uint16, uint16, uint16) envfree;
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
    function stusds.wards(address) external returns (uint256) envfree;
    function stusds.rho() external returns (uint64) envfree;
    function stusds.str() external returns (uint256) envfree;
    function stusds.line() external returns (uint256) envfree;
    function stusds.cap() external returns (uint256) envfree;
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

invariant strMin_LessOrEqual_strMax() currentContract.strCfg.min <= currentContract.strCfg.max;
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
    mathint strMinBefore; mathint strMaxBefore; mathint strStepBefore;
    strMinBefore, strMaxBefore, strStepBefore = strCfg();
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
    mathint strMinAfter; mathint strMaxAfter; mathint strStepAfter;
    strMinAfter, strMaxAfter, strStepAfter = strCfg();
    mathint dutyMinAfter; mathint dutyMaxAfter; mathint dutyStepAfter;
    dutyMinAfter, dutyMaxAfter, dutyStepAfter = dutyCfg();
    mathint maxLineAfter = maxLine();
    mathint maxCapAfter = maxCap();
    mathint badAfter = bad();
    mathint tauAfter = tau();
    mathint tocAfter = toc();

    assert wardsAfter != wardsBefore => f.selector == sig:rely(address).selector || f.selector == sig:deny(address).selector, "Assert 1";
    assert budsAfter != budsBefore => f.selector == sig:kiss(address).selector || f.selector == sig:diss(address).selector, "Assert 2";
    assert strMinAfter != strMinBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 3";
    assert strMaxAfter != strMaxBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 4";
    assert strStepAfter != strStepBefore => f.selector == sig:file(bytes32, bytes32, uint256).selector, "Assert 5";
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
    require ilk != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000);

    mathint strMinBefore; mathint strMaxBefore; mathint strStepBefore;
    strMinBefore, strMaxBefore, strStepBefore = strCfg();
    mathint dutyMinBefore; mathint dutyMaxBefore; mathint dutyStepBefore;
    dutyMinBefore, dutyMaxBefore, dutyStepBefore = dutyCfg();

    file(e, id, what, data);

    mathint strMinAfter; mathint strMaxAfter; mathint strStepAfter;
    strMinAfter, strMaxAfter, strStepAfter = strCfg();
    mathint dutyMinAfter; mathint dutyMaxAfter; mathint dutyStepAfter;
    dutyMinAfter, dutyMaxAfter, dutyStepAfter = dutyCfg();

    assert id == to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) &&
           what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) => strMinAfter == to_mathint(data), "Assert 1";
    assert id != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) ||
           what != to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) => strMinAfter == strMinBefore, "Assert 2";
    assert id == to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) &&
           what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) => strMaxAfter == to_mathint(data), "Assert 3";
    assert id != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) ||
           what != to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) => strMaxAfter == strMaxBefore, "Assert 4";
    assert id == to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) &&
           what == to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000) => strStepAfter == to_mathint(data), "Assert 5";
    assert id != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) ||
           what != to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000) => strStepAfter == strStepBefore, "Assert 6";
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
    require ilk != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000);

    mathint wardsSender = wards(e.msg.sender);
    mathint strMin; mathint strMax; mathint a;
    strMin, strMax, a = strCfg();
    mathint dutyMin; mathint dutyMax;
    dutyMin, dutyMax, a = dutyCfg();

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;
    bool revert3 = id != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) &&
                   id != ilk;
    bool revert4 = to_mathint(data) > max_uint16;
    bool revert5 = what != to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) &&
                   what != to_bytes32(0x7374657000000000000000000000000000000000000000000000000000000000);
    bool revert6 = id == to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) &&
                   what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) > strMax;
    bool revert7 = id == ilk &&
                   what == to_bytes32(0x6d696e0000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) > dutyMax;
    bool revert8 = id == to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000) &&
                   what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) < strMin;
    bool revert9 = id == ilk &&
                   what == to_bytes32(0x6d61780000000000000000000000000000000000000000000000000000000000) &&
                   to_mathint(data) < dutyMin;

    file@withrevert(e, id, what, data);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7 || revert8 || revert9, "Revert rules failed";
}

// Verify correct storage changes for non reverting set
rule set(uint256 strBps, uint256 dutyBps, uint256 line, uint256 cap) {
    env e;
    bytes32 ilk = ilk();
    require ilk != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000);

    mathint rhoBefore = stusds.rho();
    mathint jRhoBefore; mathint a;
    a, jRhoBefore = jug.ilks(ilk);

    mathint strRAY = conv.btor(strBps);
    mathint dutyRAY = conv.btor(dutyBps);

    set(e, strBps, dutyBps, line, cap);

    mathint strAfter = stusds.str();
    mathint rhoAfter = stusds.rho();
    mathint dutyAfter; mathint jRhoAfter;
    dutyAfter, jRhoAfter = jug.ilks(ilk);
    mathint lineAfter = stusds.line();
    mathint capAfter = stusds.cap();

    assert rhoAfter == e.block.timestamp, "Assert 1";
    assert strAfter == strRAY, "Assert 2";
    assert jRhoAfter == e.block.timestamp, "Assert 3";
    assert dutyAfter == dutyRAY, "Assert 4";
    assert lineAfter == line, "Assert 5";
    assert capAfter == cap, "Assert 6";
    satisfy rhoBefore < rhoAfter, "Satisfy 1"; // Proves that stusds.drip() gets called
    satisfy jRhoBefore < jRhoAfter, "Satisfy 2"; // Proves that jug.drip(ilk) gets called
}

// Verify revert rules on set
rule set_revert(uint256 strBps, uint256 dutyBps, uint256 line, uint256 cap) {
    env e;

    bytes32 ilk = ilk();
    require ilk != to_bytes32(0x5354520000000000000000000000000000000000000000000000000000000000);

    mathint budsSender = buds(e.msg.sender);
    mathint bad = bad();
    mathint maxLine = maxLine();
    mathint maxCap = maxCap();
    mathint tau = tau();
    mathint toc = toc();
    mathint strMin; mathint strMax; mathint strStep;
    strMin, strMax, strStep = strCfg();
    mathint dutyMin; mathint dutyMax; mathint dutyStep;
    dutyMin, dutyMax, dutyStep = dutyCfg();

    mathint rho = stusds.rho();
    uint256 str = stusds.str();
    uint256 duty; mathint jRho;
    duty, jRho = jug.ilks(ilk);

    mathint strOldBps = conv.rtob(str) < strMin ? strMin : (conv.rtob(str) > strMax ? strMax : conv.rtob(str));
    mathint dutyOldBps = conv.rtob(duty) < dutyMin ? dutyMin : (conv.rtob(duty) > dutyMax ? dutyMax : conv.rtob(duty));
    mathint dutyDelta = dutyBps > dutyOldBps ? dutyBps - dutyOldBps : dutyOldBps - dutyBps;
    mathint strDelta = strBps > strOldBps ? strBps - strOldBps : strOldBps - strBps;

    mathint strRAY = conv.btor(strBps);
    mathint dutyRAY = conv.btor(dutyBps);

    requireInvariant strMin_LessOrEqual_strMax;
    requireInvariant dutyMin_LessOrEqual_dutyMax;

    // Happening in init scripts
    require stusds.wards(currentContract) == 1;
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
    bool revert6  = line > maxLine;
    bool revert7  = cap > maxCap;
    bool revert8  = strStep == 0;
    bool revert9  = strBps < strMin;
    bool revert10 = strBps > strMax;
    bool revert11 = strDelta > strStep;
    bool revert12 = strRAY < RAY(); // This actually doesn't trigger as conv used won't return that value
    bool revert13 = dutyStep == 0;
    bool revert14 = dutyBps < dutyMin;
    bool revert15 = dutyBps > dutyMax;
    bool revert16 = dutyDelta > dutyStep;
    bool revert17 = dutyRAY < RAY();

    storage initial = lastStorage;

    // Filter out all the reverts happening in both drip calls
    stusds.drip(e);
    jug.drip(e, ilk);
    
    set@withrevert(e, strBps, dutyBps, line, cap) at initial;

    assert lastReverted <=> revert1  || revert2  || revert3  ||
                            revert4  || revert5  || revert6  ||
                            revert7  || revert8  || revert9  ||
                            revert10 || revert11 || revert12 ||
                            revert13 || revert14 || revert15 ||
                            revert16 || revert17 , "Revert rules failed";
}
