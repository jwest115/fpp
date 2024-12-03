// ======================================================================
// \title  CommandsTopologyAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for Commands topology
// ======================================================================

#include "CommandsTopologyAc.hpp"

// ----------------------------------------------------------------------
// Component instances
// ----------------------------------------------------------------------

namespace M {

  M::C c1(FW_OPTIONAL_NAME("c1"));

}

namespace M {

  M::C c2(FW_OPTIONAL_NAME("c2"));

}

namespace M {


  // ----------------------------------------------------------------------
  // Helper functions
  // ----------------------------------------------------------------------

  void initComponents(const TopologyState& state) {
    M::c1.init(InstanceIds::M_c1);
    M::c2.init(InstanceIds::M_c2);
  }

  void configComponents(const TopologyState& state) {
    // Nothing to do
  }

  void setBaseIds() {
    M::c1.setIdBase(BaseIds::M_c1);
    M::c2.setIdBase(BaseIds::M_c2);
  }

  void connectComponents() {
    // Nothing to do
  }

  void regCommands() {
    M::c1.regCommandsSpecial();
    M::c2.regCommands();
  }

  void readParameters() {
    // Nothing to do
  }

  void loadParameters() {
    // Nothing to do
  }

  void startTasks(const TopologyState& state) {
    // Nothing to do
  }

  void stopTasks(const TopologyState& state) {
    // Nothing to do
  }

  void freeThreads(const TopologyState& state) {
    // Nothing to do
  }

  void tearDownComponents(const TopologyState& state) {
    // Nothing to do
  }

  // ----------------------------------------------------------------------
  // Setup and teardown functions
  // ----------------------------------------------------------------------

  void setup(const TopologyState& state) {
    initComponents(state);
    configComponents(state);
    setBaseIds();
    connectComponents();
    regCommands();
    readParameters();
    loadParameters();
    startTasks(state);
  }

  void teardown(const TopologyState& state) {
    stopTasks(state);
    freeThreads(state);
    tearDownComponents(state);
  }

}
