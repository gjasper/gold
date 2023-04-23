#include <fstream>
#include <iomanip>
#include <iostream>
#include <regex>
#include <algorithm>
#include <sstream>
#include <assert.h>
#include "sat.hpp"

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
    for(unsigned int i = 0; i < varList.size(); i++) {
        clauses.insert(clauses.begin() + i, Clause(varList.at(i), sigList.at(i)));
    }
    return clauses;
}

std::vector<Cell> buildCells(unsigned int varsQtt, std::vector<Clause> clauses){
    std::vector<Cell> cells;
    for(unsigned int i = 0; i < clauses.size(); i++){
        std::vector<Cell> clauseCells;
        for(unsigned int j = 0; j < clauses[i].getVars().size(); j++){
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
    for(unsigned int i = 0; i < (2 * varsQtt); i++){
        Cell cell;
        cell.next = (2 * varsQtt) - i + 1;
        cell.prev = (2 * varsQtt) - i + 1;
        cells.insert(cells.begin(), cell);
    }
    cells.insert(cells.begin(), Cell());
    cells.insert(cells.begin(), Cell());
    for(unsigned int i = (2 * varsQtt + 2); i < cells.size(); i++){
        int header = cells[i].literal;
        cells[i].next = header;
        cells[i].prev = cells[header].prev;
        cells[cells[i].prev].next = i;
        cells[header].prev = i;
        cells[header].clause += 1;
    }
    return cells;
}

AlgoA::NextStep AlgoA::a1(){
    //A1 - initialize
    a = activeClauses.size();
    d = 1;
    for(unsigned int i = 0; i < a; i++){
        m.insert(m.end(), 0);
        activeClauses[i] = true;
    }
    for(unsigned int i = 0; i < varQtt * 2 + 2; i++){
        activeLiterals[i] = true;
    }
    return A2;
}

AlgoA::NextStep AlgoA::a2(){
    //A2 - choose
    l = 2 * d;
    if (cells[l].clause <= cells[l + 1].clause) {
        l++;
    }
    m[d-1] = (l & 1) + 4 * (cells[l ^ 1].clause == 0);
    // printM();
    if(cells[l].clause == a){
        return RETURN_SAT;
    }
    return A3;
}

AlgoA::NextStep AlgoA::a3(){
    //A3 - remove not l
    unsigned int nl = l ^ 1;
    unsigned int next = snext(nl);
    bool allowed = next >= varQtt * 2 + 2 ? true : false;
    while(allowed && next != nl){
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
        }
        next = snext(next);
    }
    if(allowed) {
        activeLiterals[nl] = false;
        cells[nl].clause = 0;
        return A4;
    } else {
        return A5;
    }
}

AlgoA::NextStep AlgoA::a4(){
    //A4 - deactivate l's clauses
    unsigned int pl = l;
    unsigned int next = snext(pl);
    while(next >= varQtt * 2 + 2 && next != pl){
        activeClauses[cells[next].clause - 1] = false;
        a--;
        int clause = cells[next].clause;
        for(unsigned int j = (cells.size() - 3 * clause); j < (cells.size() + CLAUSE_SIZE - CLAUSE_SIZE * clause); j++){
            if(cells[cells[j].literal].clause > 0)
                cells[cells[j].literal].clause--;
        }
        next = snext(next);
    }
    d++;
    return A2;
}

AlgoA::NextStep AlgoA::a5(){
    //A5 - try again
    if(m[d-1] < 2){
        m[d-1] = 3 - m[d-1];
        // printM();
        l = 2 * d + (m[d-1] & 1);
        return A3;
    }
    return A6;
}

AlgoA::NextStep AlgoA::a6(){
    //A6 - backtrack
    if(d == 1){
        return RETURN_UNSAT;
    } else {
        d--;
        l = 2 * d + (m[d-1] & 1);
        return A7;
    }
}

AlgoA::NextStep AlgoA::a7(){
    //A7 - reactivate l's clauses
    unsigned int next = cells[l].next;
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
    return A8;
}

AlgoA::NextStep AlgoA::a8(){
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
    return A5;
}

SatModel parseString(unsigned int varsQtt, std::string vs, std::string ss){
    std::vector<Clause> clauses = parseClauses(vs, ss);
    std::vector<Cell> cells = buildCells(varsQtt, clauses);
    return SatModel(clauses, cells, varsQtt);
}

std::vector<int> getNumbersFromString(const std::string& str)
{
    std::vector<int> result;
    std::stringstream ss(str);
    int num;
    while (ss >> num && num != 0)
    {
        result.push_back(num);
        ss.ignore();
    }
    return result;
}

SatModel parseDimacs(std::string filePath) {
    std::ifstream myfile;
    std::string line;
    myfile.open(filePath);
    std::vector<Clause> clauses;
    int varCount;
    if (myfile.is_open()) {
        while (std::getline(myfile, line) && line.at(0) != 'p'){}
        std::stringstream ss(line);
        ss.ignore(6);
        ss >> varCount;
        while (std::getline(myfile, line)){
            Clause c(getNumbersFromString(line));
            clauses.insert(clauses.end(), c);
        }
        myfile.close();
    } else std::cout << "Unable to open file";
    return SatModel(clauses, buildCells(varCount, clauses), varCount);
}

void SatModel::print() const {
    auto toString = [](int i){
        std::ostringstream str;
        str << " " << std::setw(2) << std::setfill(' ') << i;
        return str.str();
    };

    std::stringstream ss;
    for(unsigned int i = 0; i < getClauses().size(); i++){
        std::vector<std::pair<unsigned int, bool>> vars = getClauses().at(i).getVars();
        ss << (vars.at(0).second ? "  " : " -") << vars.at(0).first;
        ss << (vars.at(1).second ? "  " : " -") << vars.at(1).first;
        ss << (vars.at(2).second ? "  " : " -") << vars.at(2).first;
        ss << " ";
    }
    std::cout << ss.str();

    std::string j;
    std::string l;
    std::string f;
    std::string b;
    std::string c;
    for(unsigned int i = 0; i < cells.size(); i++){
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