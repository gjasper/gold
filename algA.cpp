#include <iostream>
#include <vector>
#include <regex>
#include <algorithm>
#include <string>
#include <sstream>
#include <iomanip>

const int CLAUSE_SIZE = 3;
const int VARS_COUNT = 4;

const std::string EQUATION_7_VARS = "123,234,341,412,123,234,341";
const std::string EQUATION_7_SIGS = "110,110,111,101,001,001,000";
const std::string EQUATION_6_VARS = "123,234,341,412,123,234,341,412";
const std::string EQUATION_6_SIGS = "110,110,111,101,001,001,000,010";

class Clause {

    private:
        std::vector<std::pair<unsigned int, bool>> vars;
    public:
        Clause(std::string vs, std::string ss) {
            vars.insert(vars.begin() + 0, std::pair((int) vs.at(0) - 48, (int) ss.at(0) - 48));
            vars.insert(vars.begin() + 1, std::pair((int) vs.at(1) - 48, (int) ss.at(1) - 48));
            vars.insert(vars.begin() + 2, std::pair((int) vs.at(2) - 48, (int) ss.at(2) - 48));
        }
        std::vector<std::pair<unsigned int, bool>> getVars(){
            return vars;
        }
};

class Cell {

    private:
    public:
        Cell(): literal(0), next(0), prev(0), clause(0){}
        unsigned int next;
        unsigned int prev;
        unsigned int literal;
        unsigned int clause;
};

std::vector<Clause> parseClauses(std::string vars, std::string sigs){
    if(vars.size() != sigs.size()){
        throw std::invalid_argument("mismatched sizes between vars and sigs");
    }
    std::vector<Clause> vs;
    std::regex regexz(",");
    std::vector<std::string> varList(std::sregex_token_iterator(vars.begin(), vars.end(), regexz, -1),
                                  std::sregex_token_iterator());
    std::vector<std::string> sigList(std::sregex_token_iterator(sigs.begin(), sigs.end(), regexz, -1),
                                  std::sregex_token_iterator());
    std::vector<Clause> clauses;
    for(int i = 0; i < varList.size(); i++) {
        clauses.insert(clauses.begin() + i, Clause(varList.at(i), sigList.at(i)));
    }
    return clauses;
}

std::vector<Cell> buildCells(unsigned int varsQtt, std::vector<Clause> clauses){
    std::vector<Cell> cells;
    for(int i = 0; i < clauses.size(); i++){
        std::vector<Cell> clauseCells;
        for(int j = 0; j < clauses[i].getVars().size(); j++){
            Cell cell;
            cell.literal = clauses[i].getVars()[j].first << 1;
            if(!clauses[i].getVars()[j].second){
                cell.literal = cell.literal ^ 1;
            }
            cell.clause = i + 1;
            clauseCells.insert(clauseCells.begin(), cell);
        }
        sort(clauseCells.begin(), clauseCells.end(), [](Cell a, Cell b){
            return a.literal < b.literal;
        });
        for(Cell cell : clauseCells){
            cells.insert(cells.begin(), cell);
        }
    }
    for(int i = 0; i < (2 * varsQtt); i++){
        Cell cell;
        cell.next = (2 * varsQtt) - i + 1;
        cell.prev = (2 * varsQtt) - i + 1;
        cells.insert(cells.begin(), cell);
    }
    cells.insert(cells.begin(), Cell());
    cells.insert(cells.begin(), Cell());
    for(int i = (2 * varsQtt + 2); i < cells.size(); i++){
        int header = cells[i].literal;
        cells[i].next = header;
        cells[i].prev = cells[header].prev;
        cells[cells[i].prev].next = i;
        cells[header].prev = i;
        cells[header].clause += 1;
    }
    return cells;
}

class SatModel {

    private:
        std::vector<Clause> clauses;
        std::vector<Cell> cells;

        class AlgoA {

            class UNSAT {

            };

            class SAT {

            };

            private:
                std::vector<bool> activeClauses;
                std::vector<bool> activeLiterals;
                std::vector<Cell> cells;
                int a;
                int d;
                int l;
                std::vector<int> m;

                bool isClauseActive(int i){
                    return activeClauses[cells[i].clause - 1];
                };

                bool isLiteralActive(int i){
                    return activeLiterals[cells[i].literal];
                };

                int snext(int i){
                    if(cells[i].next < 10 || (isClauseActive(cells[i].next) && (i < 10 || isLiteralActive(i)))){
                        return cells[i].next;
                    } else {
                        return snext(cells[i].next);
                    }
                }

                int sprev(int i){
                    if(cells[i].prev < 10 || (isClauseActive(cells[i].prev) && (i < 10 || isLiteralActive(i)))){
                        return cells[i].prev;
                    } else {
                        return sprev(cells[i].prev);
                    }
                }

                void a1(){
                    //A1 - initialize
                    a = activeClauses.size();
                    d = 1;
                    for(int i = 0; i < a; i++){
                        m.insert(m.end(), 0);
                        activeClauses[i] = true;
                    }
                    for(int i = 0; i < VARS_COUNT * 2 + 2; i++){
                        activeLiterals[i] = true;
                    }
                    a2();
                }
                void a2(){
                    //A2 - choose
                    l = 2 * d;
                    if (cells[l].clause <= cells[l + 1].clause) {
                        l++;
                    }
                    m[d-1] = (l & 1) + 4 * (cells[l ^ 1].clause == 0);
                    if(cells[l].clause == a){
                        throw new SAT();
                    }
                    a3();
                }
                void a3(){
                    //A3 - remove not l
                    int nl = l ^ 1;
                    int next = snext(nl);
                    bool allowed = true;
                    while(next > 9 && next != nl){
                        int active = 0;
                        int clause = cells[next].clause;
                        int start = cells.size() - CLAUSE_SIZE * clause;
                        int end = start + CLAUSE_SIZE;
                        for(int j = start; j < end; j++){
                            if(cells[cells[j].literal].clause > 0){
                                active++;
                            }
                        }
                        if(active <= 1){
                            allowed = false;
                            break;
                        }
                        next = snext(next);
                    }
                    if(allowed) {
                        activeLiterals[nl] = false;
                        cells[nl].clause = 0;
                        a4();
                    } else {
                        a5();
                    }
                }
                void a4(){
                    //A4 - deactivate l's clauses
                    int pl = l;
                    int next = snext(pl);
                    while(next != pl){
                        activeClauses[cells[next].clause - 1] = false;
                        a--;
                        int clause = cells[next].clause;
                        for(int j = (cells.size() - 3 * clause); j < (cells.size() + CLAUSE_SIZE - CLAUSE_SIZE * clause); j++){
                            if(cells[cells[j].literal].clause > 0)
                                cells[cells[j].literal].clause--;
                        }
                        next = snext(next);
                    }
                    d++;
                    a2();
                }
                void a5(){
                    //A5 - try again
                    if(m[d-1] < 2){
                        m[d-1] = 3 - m[d-1];
                        l = 2 * d + (m[d-1] & 1);
                        a3();
                    }
                    a6();
                }
                void a6(){
                    //A6 - backtrack
                    if(d == 1){
                        throw new UNSAT();
                    } else {
                        d--;
                        l = 2 * d + (m[d-1] & 1);
                        a7();
                    }
                }
                void a7(){
                    //A7 - reactivate l's clauses
                    int next = cells[l].next;
                    while(next != l){
                        activeClauses[cells[next].clause - 1] = true;
                        a++;
                        int clause = cells[next].clause;
                        int start = cells.size() - CLAUSE_SIZE * clause;
                        int end = start + CLAUSE_SIZE;
                        for(int j = start; j < end; j++){
                            if(activeLiterals[cells[j].literal])
                                cells[cells[j].literal].clause++;
                        }
                        next = cells[next].next;
                    }
                    a8();
                }
                void a8(){
                    //A8 - unremove not l
                    int nl = l ^ 1;
                    int next = cells[nl].next;
                    while(next != nl){
                        if(activeClauses[cells[next].clause - 1]){
                            activeLiterals[cells[next].literal] = true;
                            cells[cells[next].literal].clause++;
                        }
                        next = cells[next].next;
                    }
                    a5();
                }

            public:
                AlgoA(std::vector<Clause> cs, std::vector<Cell> csls) :
                    activeClauses(cs.size()), activeLiterals(VARS_COUNT * 2 + 2), cells(csls) {}
                bool run(){
                    try {
                        a1();
                    } catch(SAT e) {
                        return true;
                    } catch(UNSAT e) {
                        return false;
                    }
                    return false;
                }
        };

    public:
        SatModel(unsigned int varsQtt, std::string vs, std::string ss):
            clauses(parseClauses(vs, ss))
          , cells(buildCells(varsQtt, clauses)) {
        }
        std::vector<Clause> getClauses() {
            return clauses;
        }
        std::vector<Cell> getCells() {
            return cells;
        }
        bool isSat() {
            AlgoA a(clauses, cells);
            return a.run();
        }
        void print(){
            auto toString = [](int i){
                std::ostringstream str;
                str << " " << std::setw(2) << std::setfill(' ') << i;
                return str.str();
            };
            std::string j;
            std::string l;
            std::string f;
            std::string b;
            std::string c;
            for(int i = 0; i < cells.size(); i++){
                j.append(toString(i));
                l.append(toString(cells[i].literal));
                f.append(toString(cells[i].prev));
                b.append(toString(cells[i].next));
                c.append(toString(cells[i].clause));
            }
            std::cout << "\n";
            std::cout << "i: " << j << std::endl;
            std::cout << "\n";
            std::cout << "l: " << l << std::endl;
            std::cout << "f: " << f << std::endl;
            std::cout << "b: " << b << std::endl;
            std::cout << "c: " << c << std::endl;
        }

};

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