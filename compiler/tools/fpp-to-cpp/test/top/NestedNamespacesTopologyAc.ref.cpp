// ======================================================================
// \title  NestedNamespacesTopologyAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for NestedNamespaces topology
// ======================================================================

#include "NestedNamespacesTopologyAc.hpp"

// ----------------------------------------------------------------------
// Component instances
// ----------------------------------------------------------------------

M::N::O::C c(FW_OPTIONAL_NAME("c"));

namespace M {

  // ----------------------------------------------------------------------
  // Helper functions
  // ----------------------------------------------------------------------

  void initComponents(const TopologyState& state) {
    c.init(InstanceIds::c);
  }

  void configComponents(const TopologyState& state) {
    // Nothing to do
  }

  void setBaseIds() {
    c.setIdBase(BaseIds::c);
  }

  void connectComponents() {
    // Nothing to do
  }

  void regCommands() {
    // Nothing to do
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
