// ======================================================================
// \title  ActiveAsyncProductPortsOnlyTesterBase.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for ActiveAsyncProductPortsOnly component test harness base class
// ======================================================================

#ifndef ActiveAsyncProductPortsOnlyTesterBase_HPP
#define ActiveAsyncProductPortsOnlyTesterBase_HPP

#include <cstdio>

#include "Fw/Comp/PassiveComponentBase.hpp"
#include "Fw/Port/InputSerializePort.hpp"
#include "Fw/Types/Assert.hpp"
#include "Fw/Types/ExternalString.hpp"
#include "test-base/ActiveAsyncProductPortsOnlyComponentAc.hpp"

//! \class ActiveAsyncProductPortsOnlyTesterBase
//! \brief Auto-generated base for ActiveAsyncProductPortsOnly component test harness
class ActiveAsyncProductPortsOnlyTesterBase :
  public Fw::PassiveComponentBase
{

  public:

    // ----------------------------------------------------------------------
    // Component initialization
    // ----------------------------------------------------------------------

    //! Initialize object ActiveAsyncProductPortsOnlyTesterBase
    virtual void init(
        FwEnumStoreType instance = 0 //!< The instance number
    );

  public:

    // ----------------------------------------------------------------------
    // Connectors for to ports
    // ----------------------------------------------------------------------

    //! Connect port to productRecvIn[portNum]
    void connect_to_productRecvIn(
        FwIndexType portNum, //!< The port number
        Fw::InputDpResponsePort* port //!< The input port
    );

  public:

    // ----------------------------------------------------------------------
    // Getters for from ports
    // ----------------------------------------------------------------------

    //! Get from port at index
    //!
    //! \return from_productRequestOut[portNum]
    Fw::InputDpRequestPort* get_from_productRequestOut(
        FwIndexType portNum //!< The port number
    );

    //! Get from port at index
    //!
    //! \return from_productSendOut[portNum]
    Fw::InputDpSendPort* get_from_productSendOut(
        FwIndexType portNum //!< The port number
    );

  protected:

    // ----------------------------------------------------------------------
    // Component construction and destruction
    // ----------------------------------------------------------------------

    //! Construct object ActiveAsyncProductPortsOnlyTesterBase
    ActiveAsyncProductPortsOnlyTesterBase(
        const char* const compName, //!< The component name
        const U32 maxHistorySize //!< The maximum size of each history
    );

    //! Destroy object ActiveAsyncProductPortsOnlyTesterBase
    virtual ~ActiveAsyncProductPortsOnlyTesterBase();

  protected:

    // ----------------------------------------------------------------------
    // Getters for port counts
    // ----------------------------------------------------------------------

    //! Get the number of to_productRecvIn ports
    //!
    //! \return The number of to_productRecvIn ports
    FwIndexType getNum_to_productRecvIn() const;

    //! Get the number of from_productRequestOut ports
    //!
    //! \return The number of from_productRequestOut ports
    FwIndexType getNum_from_productRequestOut() const;

    //! Get the number of from_productSendOut ports
    //!
    //! \return The number of from_productSendOut ports
    FwIndexType getNum_from_productSendOut() const;

  protected:

    // ----------------------------------------------------------------------
    // Connection status queries for to ports
    // ----------------------------------------------------------------------

    //! Check whether port to_productRecvIn is connected
    //!
    //! \return Whether port to_productRecvIn is connected
    bool isConnected_to_productRecvIn(
        FwIndexType portNum //!< The port number
    );

  public:

    // ----------------------------------------------------------------------
    // Dispatching helper functions
    // ----------------------------------------------------------------------

    //! Calls component's doDispatch on behalf of the caller
    static ActiveAsyncProductPortsOnlyComponentBase::MsgDispatchStatus dispatchOne(
        ActiveAsyncProductPortsOnlyComponentBase& component //!< The component to dispatch
    );

    //! Call component's doDispatch for all current messages unless ERROR, or EXIT
    static ActiveAsyncProductPortsOnlyComponentBase::MsgDispatchStatus dispatchCurrentMessages(
        ActiveAsyncProductPortsOnlyComponentBase& component //!< The component to dispatch
    );

  private:

    // ----------------------------------------------------------------------
    // To ports
    // ----------------------------------------------------------------------

    //! To port connected to productRecvIn
    Fw::OutputDpResponsePort m_to_productRecvIn[1];

  private:

    // ----------------------------------------------------------------------
    // From ports
    // ----------------------------------------------------------------------

    //! From port connected to productRequestOut
    Fw::InputDpRequestPort m_from_productRequestOut[1];

    //! From port connected to productSendOut
    Fw::InputDpSendPort m_from_productSendOut[1];

};

#endif
