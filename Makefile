simple_smv_cosa2: simple_smv_cosa2.cpp
	$(CXX) -std=c++11 -I./utils/ -I./core/ -I./deps/smt-switch/local/include -L./build/ -L./deps/smt-switch/local/lib simple_smv_cosa2.cpp -o simple_smv_cosa2 -lcosa2 -lsmt-switch -lsmt-switch-btor

clean:
	rm -f simple_smv_cosa2
