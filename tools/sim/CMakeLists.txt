add_executable (sim Sim.cpp)
target_link_libraries (sim ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (sim bitwriter)
install(TARGETS sim RUNTIME DESTINATION bin)
