/**
 * @file ICPPDWDynamicSettings.cpp
 * @author Perun
 *
 * @version 2017-07-07
 * Created on 2017-07-07.
 */

#include "ICPPDWDynamicSettings.h"
#include "ICPPDWSettings.h"
#include "ICPUtil.h"

#include <stdlib.h>
#include <chrono>

namespace smtrat
{
  //maxContractions;targetDiameter;maxSplitNumber;gainThreshold;alpha;weightEps;minCandidates;updateFactor
  template<class Settings>
    ICPPDWDynamicSettings<Settings>::ICPPDWDynamicSettings(){
      params.open("params.par",std::ifstream::in);
      std::ofstream outfile;
      outfile.open("temp.par", std::ios_base::app);
      string line;
      std::string prefix("#");
      int isSet = 0;
      if(params.is_open() && outfile.is_open()){
         while (std::getline(params,line)){
           if (line.compare(0, prefix.size(), prefix)!=0 && isSet == 0){
              vector<string> list;
              size_t pos = 0;
              string token;
              while ((pos = line.find(";")) != string::npos) {
                token = line.substr(0, pos);
                list.push_back(token);
                line.erase(0, pos + 1);
              }
              weightEps = std::stod(list[5]);
              targetDiameter = std::stod(list[1]);
              minCandidates = std::stoi(list[6]);
              maxContractions = std::stoi(list[0]);
              gainThreshold = std::stod(list[3]);
              alpha = std::stod(list[4]);
              updateFactor = std::stod(list[7]);
              maxSplitNumber = std::stoi(list[2]);
              isSet = 1;
              std::cout << line;
              outfile << "#" << line << endl;//update the line
           }else{
              outfile << line << endl;
           }
      }
      outfile.close();
      params.close();
      remove("params.par");
      rename("temp.par","params.par" );
      begin = ICPUtil<Settings>::getTimeNow();
    }
  }
   template<class Settings>
    ICPPDWDynamicSettings<Settings>::~ICPPDWDynamicSettings(){
       std::chrono::high_resolution_clock::time_point end= ICPUtil<Settings>::getTimeNow();
       std::ofstream outfile;
       outfile.open("results.res", std::ios_base::app);
       outfile << maxContractions << ";" << targetDiameter << ";" << maxSplitNumber << ";" << gainThreshold << ";" << alpha << ";" << weightEps << ";" << minCandidates << ";" <<updateFactor;
       outfile << "==" << ICPUtil<Settings>::getDuration(begin,end) <<std::endl;;
    }

    template<class Settings>
    double ICPPDWDynamicSettings<Settings>::getWeightEps(){
      return weightEps;
    }
    template<class Settings>
    double ICPPDWDynamicSettings<Settings>::getTargetDiameter(){
      return targetDiameter;
    }
    template<class Settings>
    int ICPPDWDynamicSettings<Settings>::getMinCandidates(){
      return minCandidates;
    }
    template<class Settings>
    int ICPPDWDynamicSettings<Settings>::getMaxContractions(){
      return maxContractions;
    }
    template<class Settings>
    double ICPPDWDynamicSettings<Settings>::getGainThreshold(){
      return gainThreshold;
    }
    template<class Settings>
    double ICPPDWDynamicSettings<Settings>::getAlpha(){
      return alpha;
    }
    template<class Settings>
    double ICPPDWDynamicSettings<Settings>::getUpdateFactor(){
      return updateFactor;
    }
    template<class Settings>
    int ICPPDWDynamicSettings<Settings>::getMaxSplitNumber(){
      return maxSplitNumber;
    }



}