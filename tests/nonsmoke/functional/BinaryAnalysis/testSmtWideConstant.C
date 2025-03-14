#include <rose.h>
#include <Rose/BinaryAnalysis/SymbolicExpression.h>
#include <Rose/BinaryAnalysis/Z3Solver.h>
#include <Sawyer/Message.h>

using namespace Rose::BinaryAnalysis;
using namespace Sawyer::Message::Common;

static void test01(const std::string &solverName) {
    std::cout <<"test01: 96-bit constant\n";
    SymbolicExpression::Ptr var = SymbolicExpression::makeIntegerVariable(64+32);
    SymbolicExpression::Ptr wide = SymbolicExpression::makeIntegerConstant(64+32, 0x42);
    
    SmtSolver::Ptr solver = SmtSolver::instance(solverName);
    std::cout <<"SMT solver: " <<solver->name() <<"\n";
    solver->insert(SymbolicExpression::makeEq(wide, var));
    SmtSolver::Satisfiable sat = solver->check();
    ASSERT_always_require(SmtSolver::SAT_YES == sat);

    std::vector<std::string> vars = solver->evidenceNames();
    ASSERT_always_require(vars.size() == 1);
    std::string varName = vars[0];
    SymbolicExpression::Ptr val = solver->evidenceForName(varName);
    ASSERT_always_not_null(val);
    std::ostringstream ss;
    ss <<*val;
    ASSERT_always_require2(ss.str() == "0x000000000000000000000042[u96]",
                           "actual  : ss.str() == \"" + ss.str() + "\"");
}

static void test02(const std::string &solverName) {
    std::cout <<"test02: 160-bit constant\n";
    SymbolicExpression::Ptr var = SymbolicExpression::makeIntegerVariable(64+64+32);
    Sawyer::Container::BitVector bits(64+64+32);
    bits.fromHex("55555555_44444444_33333333_22222222_11111111");
    SymbolicExpression::Ptr wide = SymbolicExpression::makeIntegerConstant(bits);
    
    SmtSolver::Ptr solver = SmtSolver::instance(solverName);
    std::cout <<"SMT solver: " <<solver->name() <<"\n";
    solver->insert(SymbolicExpression::makeEq(wide, var));
    SmtSolver::Satisfiable sat = solver->check();
    ASSERT_always_require(SmtSolver::SAT_YES == sat);

    std::vector<std::string> vars = solver->evidenceNames();
    ASSERT_always_require(vars.size() == 1);
    std::string varName = vars[0];
    SymbolicExpression::Ptr val = solver->evidenceForName(varName);
    ASSERT_always_not_null(val);
    std::ostringstream ss;
    ss <<*val;
    ASSERT_always_require2(ss.str() == "0x5555555544444444333333332222222211111111[u160]",
                           "actual  : ss.str() == \"" + ss.str() + "\"");
}

int
main(int argc, char *argv[]) {
    ROSE_INITIALIZE;
    SmtSolver::mlog[DEBUG].enable();
    std::string solverName = argc > 1 ? argv[1] : "best";
    test01(solverName);
    test02(solverName);
}
