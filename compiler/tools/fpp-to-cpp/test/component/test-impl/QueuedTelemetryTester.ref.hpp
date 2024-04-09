// ======================================================================
// \title  QueuedTelemetryTester.hpp
// \author [user name]
// \brief  hpp file for QueuedTelemetry component test harness implementation class
// ======================================================================

#ifndef QueuedTelemetryTester_HPP
#define QueuedTelemetryTester_HPP

#include "QueuedTelemetryGTestBase.hpp"
#include "QueuedTelemetry.hpp"

class QueuedTelemetryTester :
  public QueuedTelemetryGTestBase
{

  public:

    // ----------------------------------------------------------------------
    // Constants
    // ----------------------------------------------------------------------

    // Maximum size of histories storing events, telemetry, and port outputs
    static const FwSizeType MAX_HISTORY_SIZE = 10;

    // Instance ID supplied to the component instance under test
    static const FwEnumStoreType TEST_INSTANCE_ID = 0;

    // Queue depth supplied to the component instance under test
    static const FwQueueSizeType TEST_INSTANCE_QUEUE_DEPTH = 10;

  public:

    // ----------------------------------------------------------------------
    // Construction and destruction
    // ----------------------------------------------------------------------

    //! Construct object QueuedTelemetryTester
    QueuedTelemetryTester();

    //! Destroy object QueuedTelemetryTester
    ~QueuedTelemetryTester();

  public:

    // ----------------------------------------------------------------------
    // Tests
    // ----------------------------------------------------------------------

    //! To do
    void toDo();

  private:

    // ----------------------------------------------------------------------
    // Helper functions
    // ----------------------------------------------------------------------

    //! Connect ports
    void connectPorts();

    //! Initialize components
    void initComponents();

  private:

    // ----------------------------------------------------------------------
    // Member variables
    // ----------------------------------------------------------------------

    //! The component under test
    QueuedTelemetry component;

};

#endif
