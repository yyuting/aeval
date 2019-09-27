add_executable (mu Mu.cpp)
target_link_libraries (mu ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB})
llvm_config (mu bitwriter)
install(TARGETS mu RUNTIME DESTINATION bin)
