/**
 * @file ICPPDWDynamicSettings.h
 * @author Perun
 *
 * @version 2017-07-07
 * Created on 2017-07-07.
 */

#pragma once

#include <iostream>
#include <fstream>
#include <string>


namespace smtrat{


  template<typename Settings>
    class ICPPDWDynamicSettings{
        private:
          //point in time the overall benchmark started
          std::chrono::high_resolution_clock::time_point begin;


          //required to open a filestream
          std::ifstream params;
          // number of maximal contraction per ICP state
          int maxContractions = Settings::maxContractions;

          // desired interval relative to the initial interval
          double targetDiameter = Settings::targetDiameter;

          // maximal number of splits allowed
          int maxSplitNumber = Settings::maxSplitNumber;

          //gain threshold. Best gain in contraction lower than this will result in a manual split.
          double gainThreshold = Settings::gainThreshold;

          //alpha as used in reinforced learning, see chapter 8 slide 17
          double alpha = Settings::alpha;

          //an epsilon is required to distinguish between candidates with weights which are regarded and which are not
          double weightEps = Settings::weightEps;

          //look at this many possible contraction candidates:
          int minCandidates = Settings::minCandidates;

          //this factor states how weights are updated after checkCore is called ones more
          double updateFactor = Settings::updateFactor;

        public:
          double getWeightEps();
          double getTargetDiameter();
          int getMinCandidates();
          int getMaxContractions();
          double getGainThreshold();
          double getAlpha();
          double getUpdateFactor();
          int getMaxSplitNumber();


          ICPPDWDynamicSettings();
          ~ICPPDWDynamicSettings();


    };

}

