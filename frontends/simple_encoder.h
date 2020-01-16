#pragma once

#include <stdio.h>
#include <iostream>
#include <map>
#include <string>
#include <unordered_map>


class smvEncoder{
        public: smvEncoder(std::istream &f, std::string filename){
            parse(filename);
        }

  // parse a smv file
  void parse(const std::string filename);
  std::string symbol_;
} ;
