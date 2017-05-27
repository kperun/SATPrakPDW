/**
 * @file ICPPDWStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-04-27
 * Created on 2017-04-27.
 */

#pragma once

#include "../../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
  class ICPPDWStatistics : public Statistics
  {
    private:
      // Members.
      /**
       * Example for a statistic.
       */
      int mNumberOfSplits = 0;
      int mNumberOfNodes = 0;
      int mNumberOfWrongGuesses = 0;
      int mNumberOfContractions = 0;
      double mSumOfContractions = 0.0;
      int mNumberOfIterations = 0;


    public:
      // Override Statistics::collect.
      void collect(){
        Statistics::addKeyValuePair( "Number of performed splits", mNumberOfSplits );
        Statistics::addKeyValuePair( "Number of checked nodes", mNumberOfNodes );
        Statistics::addKeyValuePair( "Number of wrong solution guesses", mNumberOfWrongGuesses);
        Statistics::addKeyValuePair( "Number of performed contractions", mNumberOfContractions);
        Statistics::addKeyValuePair( "Overall contraction diameter", mSumOfContractions);
        Statistics::addKeyValuePair( "Average contraction gain", mSumOfContractions/mNumberOfContractions);
      }

      ICPPDWStatistics( const std::string& _statisticName ):
        Statistics( _statisticName, this ){}
      ~ICPPDWStatistics(){}

      void increaseNumberOfIterations(){
        mNumberOfIterations++;
      }

      void increaseNumberOfSplits(){
        mNumberOfSplits++;
      }

      void increaseNumberOfNodes(){
        mNumberOfNodes++;
      }

      void increaseNumberOfWrongGuesses(){
        mNumberOfWrongGuesses++;
      }

      void increaseNumberOfContractions(){
        mNumberOfContractions++;
      }

      void addContractionGain(double gain){
        mSumOfContractions+= gain;
      }
  };
}

#endif
