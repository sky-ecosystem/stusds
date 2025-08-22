// StUsdsMom.spec

using StUsds as stusds;
using StUsdsRateSetter as rateSetter;

methods {
    // storage variables
    function owner() external returns (address) envfree;
    function authority() external returns (address) envfree;
    // immutables
    function stusds() external returns (address) envfree;
    //
    function stusds.wards(address) external returns (uint256) envfree;
    function stusds.line() external returns (uint256) envfree;
    function rateSetter.wards(address) external returns (uint256) envfree;
    function rateSetter.buds(address) external returns (uint256) envfree;
    function rateSetter.bad() external returns (uint8) envfree;
    function rateSetter.maxCap() external returns (uint256) envfree;
    function rateSetter.maxLine() external returns (uint256) envfree;
    function stusds.cap() external returns (uint256) envfree;
    //
    function _.diss(address) external => DISPATCHER(true);
    function _.file(bytes32, uint256) external => DISPATCHER(true);
    function _.canCall(address, address, bytes4) external => canCallSummary() expect bool;
}

persistent ghost bool retCanCall;
function canCallSummary() returns bool {
    env e;
    return retCanCall;
}

// Verify no more entry points exist
rule entryPoints(method f) filtered { f -> !f.isView } {
    env e;

    calldataarg args;
    f(e, args);

    assert f.selector == sig:setOwner(address).selector ||
           f.selector == sig:setAuthority(address).selector ||
           f.selector == sig:dissRateSetterBud(address,address).selector ||
           f.selector == sig:haltRateSetter(address).selector ||
           f.selector == sig:zeroCap(address).selector ||
           f.selector == sig:zeroLine(address).selector;
}

// Verify that each storage variable is only modified in the expected functions
rule storage_affected(method f) {
    env e;

    address ownerBefore = owner();
    address authorityBefore = authority();

    calldataarg args;
    f(e, args);

    address ownerAfter = owner();
    address authorityAfter = authority();

    assert ownerAfter != ownerBefore => f.selector == sig:setOwner(address).selector, "Assert 1";
    assert authorityAfter != authorityBefore => f.selector == sig:setAuthority(address).selector, "Assert 2";
}

// Verify correct storage changes for non reverting setOwner
rule setOwner(address owner_) { 
    env e;

    setOwner(e, owner_);

    address ownerAfter = owner();

    assert ownerAfter == owner_, "Assert 1";
}

// Verify revert rules on setOwner
rule setOwner_revert(address owner_) {
    env e;

    address owner = owner();

    setOwner@withrevert(e, owner_);

    bool revert1 = e.msg.value > 0;
    bool revert2 = owner != e.msg.sender;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting setAuthority
rule setAuthority(address authority_) { 
    env e;

    setAuthority(e, authority_);

    address authorityAfter = authority();

    assert authorityAfter == authority_, "Assert 1";
}

// Verify revert rules on setAuthority
rule setAuthority_revert(address authority_) {
    env e;

    address owner = owner();

    setAuthority@withrevert(e, authority_);

    bool revert1 = e.msg.value > 0;
    bool revert2 = owner != e.msg.sender;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting dissRateSetterBud
rule dissRateSetterBud(address rateSetter_, address bud) {
    env e;

    require rateSetter_ == rateSetter;

    dissRateSetterBud(e, rateSetter_, bud);

    mathint rateSetterBudsBudAfter = rateSetter.buds(bud);

    assert rateSetterBudsBudAfter == 0, "Assert 1";
}

// Verify revert rules on dissRateSetterBud
rule dissRateSetterBud_revert(address rateSetter_, address bud) {
    env e;

    require rateSetter_ == rateSetter;

    address owner = owner();
    address authority = authority();

    // Happening in init scripts
    require rateSetter.wards(currentContract) == 1;

    dissRateSetterBud@withrevert(e, rateSetter_, bud);

    bool revert1 = e.msg.value > 0;
    bool revert2 = owner != e.msg.sender && (authority == 0 || !retCanCall);

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting haltRateSetter
rule haltRateSetter(address rateSetter_) {
    env e;

    require rateSetter_ == rateSetter;

    haltRateSetter(e, rateSetter_);

    mathint rateSetterBadAfter = rateSetter.bad();

    assert rateSetterBadAfter == 1, "Assert 1";
}

// Verify revert rules on haltRateSetter
rule haltRateSetter_revert(address rateSetter_) {
    env e;

    require rateSetter_ == rateSetter;

    address owner = owner();
    address authority = authority();

    // Happening in init scripts
    require rateSetter.wards(currentContract) == 1;

    haltRateSetter@withrevert(e, rateSetter_);

    bool revert1 = e.msg.value > 0;
    bool revert2 = owner != e.msg.sender && (authority == 0 || !retCanCall);

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting zeroCap
rule zeroCap(address rateSetter_) {
    env e;

    require rateSetter_ == rateSetter;

    zeroCap(e, rateSetter_);

    mathint rateSetterMaxCapAfter = rateSetter.maxCap();
    mathint stusdsCapAfter = stusds.cap();

    assert rateSetterMaxCapAfter == 0, "Assert 1";
    assert stusdsCapAfter == 0, "Assert 2";
}

// Verify revert rules on zeroCap
rule zeroCap_revert(address rateSetter_) {
    env e;

    require rateSetter_ == rateSetter;

    address owner = owner();
    address authority = authority();

    // Happening in init scripts
    require stusds.wards(currentContract) == 1;
    require rateSetter.wards(currentContract) == 1;

    zeroCap@withrevert(e, rateSetter_);

    bool revert1 = e.msg.value > 0;
    bool revert2 = owner != e.msg.sender && (authority == 0 || !retCanCall);

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting zeroLine
rule zeroLine(address rateSetter_) {
    env e;

    require rateSetter_ == rateSetter;

    zeroLine(e, rateSetter_);

    mathint rateSetterMaxLineAfter = rateSetter.maxLine();
    mathint stusdsLineAfter = stusds.line();

    assert rateSetterMaxLineAfter == 0, "Assert 1";
    assert stusdsLineAfter == 0, "Assert 2";
}

// Verify revert rules on zeroLine
rule zeroLine_revert(address rateSetter_) {
    env e;

    require rateSetter_ == rateSetter;

    address owner = owner();
    address authority = authority();

    // Happening in init scripts
    require stusds.wards(currentContract) == 1;
    require rateSetter.wards(currentContract) == 1;

    zeroLine@withrevert(e, rateSetter_);

    bool revert1 = e.msg.value > 0;
    bool revert2 = owner != e.msg.sender && (authority == 0 || !retCanCall);

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}
