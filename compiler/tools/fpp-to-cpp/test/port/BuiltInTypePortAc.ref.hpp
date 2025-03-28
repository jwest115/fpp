// ======================================================================
// \title  BuiltInTypePortAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for BuiltInType port
// ======================================================================

#ifndef BuiltInTypePortAc_HPP
#define BuiltInTypePortAc_HPP

#include <cstdio>
#include <cstring>
#include <FpConfig.hpp>

#include "Fw/Comp/PassiveComponentBase.hpp"
#include "Fw/Port/InputPortBase.hpp"
#include "Fw/Port/OutputPortBase.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

//! Input BuiltInType port
//! A port with built-in type parameters
class InputBuiltInTypePort :
  public Fw::InputPortBase
{

  public:

    // ----------------------------------------------------------------------
    // Constants
    // ----------------------------------------------------------------------

    enum {
      //! The size of the serial representations of the port arguments
      SERIALIZED_SIZE =
        sizeof(FwOpcodeType) +
        sizeof(FwOpcodeType)
    };

  public:

    // ----------------------------------------------------------------------
    // Types
    // ----------------------------------------------------------------------

    //! The port callback function type
    typedef void (*CompFuncPtr)(
      Fw::PassiveComponentBase* callComp,
      FwIndexType portNum,
      FwOpcodeType t,
      FwOpcodeType& tRef
    );

  public:

    // ----------------------------------------------------------------------
    // Input Port Member functions
    // ----------------------------------------------------------------------

    //! Constructor
    InputBuiltInTypePort();

    //! Initialization function
    void init();

    //! Register a component
    void addCallComp(
        Fw::PassiveComponentBase* callComp, //!< The containing component
        CompFuncPtr funcPtr //!< The port callback function
    );

    //! Invoke a port interface
    void invoke(
        FwOpcodeType t,
        FwOpcodeType& tRef
    );

  private:

#if FW_PORT_SERIALIZATION == 1

    //! Invoke the port with serialized arguments
    Fw::SerializeStatus invokeSerial(Fw::SerializeBufferBase& _buffer);

#endif

  private:

    // ----------------------------------------------------------------------
    // Member variables
    // ----------------------------------------------------------------------

    //! The pointer to the port callback function
    CompFuncPtr m_func;

};

//! Output BuiltInType port
//! A port with built-in type parameters
class OutputBuiltInTypePort :
  public Fw::OutputPortBase
{

  public:

    // ----------------------------------------------------------------------
    // Output Port Member functions
    // ----------------------------------------------------------------------

    //! Constructor
    OutputBuiltInTypePort();

    //! Initialization function
    void init();

    //! Register an input port
    void addCallPort(
        InputBuiltInTypePort* callPort //!< The input port
    );

    //! Invoke a port interface
    void invoke(
        FwOpcodeType t,
        FwOpcodeType& tRef
    ) const;

  private:

    // ----------------------------------------------------------------------
    // Member variables
    // ----------------------------------------------------------------------

    //! The pointer to the input port
    InputBuiltInTypePort* m_port;

};

#endif
