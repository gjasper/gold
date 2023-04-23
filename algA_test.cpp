#include "sat.hpp"

const std::string EQUATION_7_VARS = "123,234,341,412,123,234,341";
const std::string EQUATION_7_SIGS = "110,110,111,101,001,001,000";
const std::string EQUATION_6_VARS = "123,234,341,412,123,234,341,412";
const std::string EQUATION_6_SIGS = "110,110,111,101,001,001,000,010";

int main() {
    auto assertThat = [](std::string msg, bool condition){
        if (condition) {
            std::cout << "SUCCESS: " << msg << std::endl;
        } else {
            std::cout << "FAILURE: " << msg << std::endl;
        }
    };

    SatModel equation6Model(VARS_COUNT, EQUATION_6_VARS, EQUATION_6_SIGS);
    SatModel equation7Model(VARS_COUNT, EQUATION_7_VARS, EQUATION_7_SIGS);

    equation6Model.print();

    assertThat("parsing: book's equation 7 equation should have 7 clauses", equation7Model.getClauses().size() == 7);

    assertThat("parsing: clause 0 should have 1 at 0", equation7Model.getClauses()[0].getVars()[0].first == 1);
    assertThat("parsing: clause 0 should have true at 0", equation7Model.getClauses()[0].getVars()[0].second);

    assertThat("parsing: clause 6 should have 1 at 2", equation7Model.getClauses()[6].getVars()[2].first == 1);
    assertThat("parsing: clause 6 should have false at 2", !equation7Model.getClauses()[6].getVars()[2].second);

    assertThat("modeling: book's equation 7 should have 31 cells", equation7Model.getCells().size() == 31);
    assertThat("modeling: cell 9 should have nothing as literal", equation7Model.getCells()[9].literal == 0);
    assertThat("modeling: cell 9 should have 25 as next", equation7Model.getCells()[9].prev == 25);
    assertThat("modeling: cell 9 should have 10 as previous", equation7Model.getCells()[9].next == 10);
    assertThat("modeling: cell 9 should have 2 as clause", equation7Model.getCells()[9].clause == 2);

    assertThat("modeling: cell 10 equation should have 9 as literal", equation7Model.getCells()[10].literal == 9);
    assertThat("modeling: cell 10 equation should have 9 as next", equation7Model.getCells()[10].prev == 9);
    assertThat("modeling: cell 10 equation should have 25 as previous", equation7Model.getCells()[10].next == 25);
    assertThat("modeling: cell 10 equation should have 7 as clause", equation7Model.getCells()[10].clause == 7);

    assertThat("modeling: cell 30 equation should have 2 as literal", equation7Model.getCells()[30].literal == 2);
    assertThat("modeling: cell 30 equation should have 24 as next", equation7Model.getCells()[30].prev == 24);
    assertThat("modeling: cell 30 equation should have 2 as previous", equation7Model.getCells()[30].next == 2);
    assertThat("modeling: cell 30 equation should have 1 as clause", equation7Model.getCells()[30].clause == 1);

    assertThat("solving: book's equation 7 should be sat", equation7Model.isSat());
    assertThat("solving: book's equation 6 should be unsat", !equation6Model.isSat());
}