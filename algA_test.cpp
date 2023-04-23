#include <iostream>
#include "sat.hpp"

const std::string EQUATION_7_VARS = "123,234,341,412,123,234,341";
const std::string EQUATION_7_SIGS = "110,110,111,101,001,001,000";
const std::string EQUATION_6_VARS = "123,234,341,412,123,234,341,412";
const std::string EQUATION_6_SIGS = "110,110,111,101,001,001,000,010";
const std::string EQUATION_6_FILE_PATH = "equation6.cnf";
const std::string EQUATION_7_FILE_PATH = "equation7.cnf";
const int VARS_COUNT = 4;

void assertThat(std::string msg, bool condition){
    if (condition) {
        std::cout << "SUCCESS: " << msg << std::endl;
    } else {
        std::cout << "FAILURE: " << msg << std::endl;
    }
}

void assertDataStructure(const SatModel& model){
    std::cout << "\nStarting data structure assertions..." << std::endl;
    model.print();
    assertThat("parsing: book's equation 7 equation should have 4 vars", model.getVarQtt() == 4);
    assertThat("parsing: book's equation 7 equation should have 7 clauses", model.getClauses().size() == 7);

    assertThat("parsing: clause 0 should have 1 at 0", model.getClauses()[0].getVars()[0].first == 1);
    assertThat("parsing: clause 0 should have true at 0", model.getClauses()[0].getVars()[0].second);

    assertThat("parsing: clause 6 should have 1 at 2", model.getClauses()[6].getVars()[2].first == 1);
    assertThat("parsing: clause 6 should have false at 2", !model.getClauses()[6].getVars()[2].second);

    assertThat("modeling: book's equation 7 should have 31 cells", model.getCells().size() == 31);
    assertThat("modeling: cell 9 should have nothing as literal", model.getCells()[9].literal == 0);
    assertThat("modeling: cell 9 should have 25 as next", model.getCells()[9].prev == 25);
    assertThat("modeling: cell 9 should have 10 as previous", model.getCells()[9].next == 10);
    assertThat("modeling: cell 9 should have 2 as clause", model.getCells()[9].clause == 2);

    assertThat("modeling: cell 10 equation should have 9 as literal", model.getCells()[10].literal == 9);
    assertThat("modeling: cell 10 equation should have 9 as next", model.getCells()[10].prev == 9);
    assertThat("modeling: cell 10 equation should have 25 as previous", model.getCells()[10].next == 25);
    assertThat("modeling: cell 10 equation should have 7 as clause", model.getCells()[10].clause == 7);

    assertThat("modeling: cell 30 equation should have 2 as literal", model.getCells()[30].literal == 2);
    assertThat("modeling: cell 30 equation should have 24 as next", model.getCells()[30].prev == 24);
    assertThat("modeling: cell 30 equation should have 2 as previous", model.getCells()[30].next == 2);
    assertThat("modeling: cell 30 equation should have 1 as clause", model.getCells()[30].clause == 1);
}

int main() {
    SatModel equation6ModelFromString = parseString(VARS_COUNT, EQUATION_6_VARS, EQUATION_6_SIGS);
    SatModel equation7ModelFromString = parseString(VARS_COUNT, EQUATION_7_VARS, EQUATION_7_SIGS);
    SatModel equation6ModelFromDimacs = parseDimacs(EQUATION_6_FILE_PATH);
    SatModel equation7ModelFromDimacs = parseDimacs(EQUATION_7_FILE_PATH);
    assertDataStructure(equation7ModelFromString);
    assertDataStructure(equation7ModelFromDimacs);
    assertThat("solving: book's equation 6 should be unsat", !equation6ModelFromString.isSat());
    assertThat("solving: book's equation 7 should be sat", equation7ModelFromString.isSat());
    assertThat("solving: book's equation 6 should be unsat", !equation6ModelFromDimacs.isSat());
    assertThat("solving: book's equation 7 should be sat", equation7ModelFromDimacs.isSat());
    assertThat("solving: CBS_k3_n100_m423_b10_82 should be sat", parseDimacs("CBS_k3_n100_m423_b10_82.cnf").isSat());
    assertThat("solving: dubois20 should be unsat", !parseDimacs("dubois20.cnf").isSat());
    assertThat("solving: aim-50-1_6-yes1-4 should be sat", parseDimacs("aim-50-1_6-yes1-4.cnf").isSat());
    assertThat("solving: aim-100-1_6-no-1 should be unsat", !parseDimacs("aim-100-1_6-no-1.cnf").isSat());
}