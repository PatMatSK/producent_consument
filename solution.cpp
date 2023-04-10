#ifndef __PROGTEST__
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <climits>
#include <cfloat>
#include <cassert>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <algorithm>
#include <numeric>
#include <string>
#include <vector>
#include <array>
#include <iterator>
#include <set>
#include <list>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <stack>
#include <deque>
#include <memory>
#include <functional>
#include <thread>
#include <mutex>
#include <atomic>
#include <chrono>
#include <stdexcept>
#include <condition_variable>
#include <pthread.h>
#include <semaphore.h>
#include <unistd.h>
#include "progtest_solver.h"
#include "sample_tester.h"
using namespace std;
#endif /* __PROGTEST__ */





///-------------------------------------------------------------------------------------------------------------------------------------------------------------
///-------------------------------------------------------------------------------------------------------------------------------------------------------------
///-------------------------------------------------------------------------------------------------------------------------------------------------------------
class COptimizer
{
public:
    COptimizer():id_company_gen(0){}
    static bool                        usingProgtestSolver                     ( void )
    {
        return true;
    }
    static void                        checkAlgorithm                          ( AProblem                              problem )
    {
        // dummy implementation if usingProgtestSolver() returns true
    }
    void                               start                                   ( int                                   threadCount );
    void                               stop                                    ( void );
    void                               addCompany                              ( ACompany                              company );
private:
    class CRental
    {
    public:
        explicit CRental( ACompany & a, int i): me(a), id(i), running(true){}
        ACompany                            me;
        int                                 id;
        bool                                running;
        condition_variable                  cv_company;
        mutex                               mux_company;
        map<int, pair<int, AProblemPack>>   apa;  // <id, <status, pack>>
    };
    vector<shared_ptr<CRental>>         companies;
    vector<thread>                      calculators;
    vector<thread>                      inputs;
    vector<thread>                      outputs;
    int                                 id_company_gen;
    list<pair<pair<int, int>, AProblem>>problems;      //  <<id_company, id_packet>, AProblem>
    mutex                               mux_problems;
    condition_variable                  cv_problems;
    void                                receiver                               ( int id_company );
    void                                sender                                 ( int id_company );
    void                                worker                                 ( );
};


/// ---------------------------------------------------------------------------------------------------------
void COptimizer::addCompany(ACompany company)
{
    companies.push_back(make_shared<CRental> (company, id_company_gen++));
}


/// ----------------------------------------------------------------------------------------------------------
void COptimizer::start(int threadCount)
{
    for (auto & oneCom : companies)
    {
        inputs.emplace_back(&COptimizer::receiver, this, oneCom->id);
        outputs.emplace_back(&COptimizer::sender, this, oneCom->id);
    }

    for (int i = 0; i < threadCount; i++)
        calculators.emplace_back(thread(&COptimizer::worker, this));
}


/// ----------------------------------------------------------------------------------------------------------
/// wait for all calculators and shut all threads
void COptimizer::stop()
{

    for (auto & rcvr : inputs)
        rcvr.join();

    for (auto & sndr : outputs)
        sndr.join();

    for (auto & wrkr : calculators)
        wrkr.join();

}


///--------------------------------------------------------------------------------------------------------------------
///--------------------------------------------------------------------------------------------------------------------
///--------------------------------------------------------------------------------------------------------------------
/// wait for packets and send them to calculators also inform output about sequence of packets
/// get Problem pack unzip it, add problems to problemque
void COptimizer::receiver( int id_company )
{
    int id_packet = 0;
    while( companies[id_company]->running )
    {
        AProblemPack packet = companies[id_company]->me->waitForPack();

        if ( !packet )
        {
            unique_lock<mutex> l2 (mux_problems);
            id_company_gen--;
            cv_problems.notify_all();
            l2.unlock();
            unique_lock<mutex> l1 (companies[id_company]->mux_company);
            companies[id_company]->running = false;
            companies[id_company]->cv_company.notify_all();
            l1.unlock();
            return;
        }

        unique_lock<mutex> l1 (companies[id_company]->mux_company);
        companies[id_company]->apa.insert({id_packet, make_pair( packet->m_Problems.size(), packet)});
        l1.unlock();
        /// -------------------------------------- last set of problems -----------------------------------------
        unique_lock<mutex> l2 (mux_problems);
        for ( auto & i : packet->m_Problems )
            problems.push_back(make_pair(make_pair(id_company, id_packet), i));
        cv_problems.notify_one();
        l2.unlock();

        id_packet++;
    }
}


///--------------------------------------------------------------------------------------------------------------------
///--------------------------------------------------------------------------------------------------------------------
///--------------------------------------------------------------------------------------------------------------------
/// receive solutions and in correct order send answers
void COptimizer::sender( int id_company )
{
    int id_packet = 0;
    while ( companies[id_company]->running || ! companies[id_company]->apa.empty() )
    {
        unique_lock<mutex> l (companies[id_company]->mux_company);
        while ( companies[id_company]->apa.empty()
                || companies[id_company]->apa[id_packet].first ) // do not have packets or first is not solved
        {
            if ( ! companies[id_company]->running && companies[id_company]->apa.empty() )
                return;
            companies[id_company]->cv_company.wait(l);
        }

        companies[id_company]->me->solvedPack(companies[id_company]->apa[id_packet].second);
        companies[id_company]->apa.erase(id_packet);
        companies[id_company]->cv_company.notify_all();
        l.unlock();
        id_packet++;
    }
}

///--------------------------------------------------------------------------------------------------------------------
///--------------------------------------------------------------------------------------------------------------------
///--------------------------------------------------------------------------------------------------------------------
/// wait for pack from input and then do meth
void COptimizer::worker( )
{
    vector<pair<int, int>> currently_solving;
    AProgtestSolver ps;
    while ( id_company_gen || !problems.empty() )
    {
        /// ------------------------------------------------- pick up problems -----------------------------------------
        ps = createProgtestSolver();
        currently_solving.clear();
        unique_lock<mutex> l1 (mux_problems);
        while ( problems.empty() && id_company_gen )
            cv_problems.wait(l1);
        while ( ps->hasFreeCapacity() )
        {
            while ( problems.empty() && id_company_gen )
                cv_problems.wait(l1);

            if ( ! id_company_gen && problems.empty() )   // terminate command
                break;

            ps->addProblem(problems.front().second);
            currently_solving.push_back(problems.front().first);
            problems.pop_front();
        }

        if ( currently_solving.empty() && problems.empty() && id_company_gen == 0 )
            return;

        cv_problems.notify_one();
        l1.unlock();
        /// ------------------------------------------------- solve problems -------------------------------------------
        ps->solve();
        /// -------------------------------------------- notify about solved problems ----------------------------------
        for ( auto & i : currently_solving )
        {
            unique_lock<mutex> l2 ( companies[i.first]->mux_company);
            auto it = companies[i.first]->apa.find(i.second);
            it->second.first--;
            if ( it->second.first == 0 )
                companies[i.first]->cv_company.notify_all();
            l2.unlock();
        }
        /// ----------------------------------------------------- again ------------------------------------------------
    }
}



// TODO: COptimizer implementation goes here
//----------------------------------------------------------------------------------------------------------------------
#ifndef __PROGTEST__
int                                    main                                    ( void )
{
    COptimizer optimizer;
    ACompanyTest  company = std::make_shared<CCompanyTest> ();
    ACompanyTest  company2 = std::make_shared<CCompanyTest> ();
    // ACompanyTest  company3 = std::make_shared<CCompanyTest> ();
    // ACompanyTest  company4 = std::make_shared<CCompanyTest> ();
    // ACompanyTest  company5 = std::make_shared<CCompanyTest> ();
    optimizer . addCompany ( company );
    optimizer . addCompany ( company2 );
    // optimizer . addCompany ( company3 );
    // optimizer . addCompany ( company4 );
    // optimizer . addCompany ( company5 );
    optimizer . start ( 4 );
    optimizer . stop  ();

    if ( ! company -> allProcessed () )
        throw std::logic_error ( "(some) problems were not correctly processed" );

    if ( ! company2 -> allProcessed () )
        throw std::logic_error ( "(some) problems were not correctly processed2" );
    /*

    if ( ! company3 -> allProcessed () )
        throw std::logic_error ( "(some) problems were not correctly processed3" );

    if ( ! company4 -> allProcessed () )
        throw std::logic_error ( "(some) problems were not correctly processed4" );

    if ( ! company5 -> allProcessed () )
        throw std::logic_error ( "(some) problems were not correctly processed5" );
    */

    printf("\n    GOOD JOB SHERIFF\n\n");

    return 0;
}
#endif /* __PROGTEST__ */
