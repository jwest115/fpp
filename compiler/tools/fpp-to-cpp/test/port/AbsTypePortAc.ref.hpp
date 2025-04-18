// ======================================================================
// \title  AbsTypePortAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for AbsType port
// ======================================================================

#ifndef AbsTypePortAc_HPP
#define AbsTypePortAc_HPP

#include <cstdio>
#include <cstring>

#include "Fw/Comp/PassiveComponentBase.hpp"
#include "Fw/FPrimeBasicTypes.hpp"
#include "Fw/Port/InputPortBase.hpp"
#include "Fw/Port/OutputPortBase.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"
#include "include/T.hpp"

//! Input AbsType port
//! A port with abstract type parameters
class InputAbsTypePort :
  public Fw::InputPortBase
{

  public:

    // ----------------------------------------------------------------------
    // Constants
    // ----------------------------------------------------------------------

    enum {
      //! The size of the serial representations of the port arguments
      SERIALIZED_SIZE =
        T::SERIALIZED_SIZE +
        T::SERIALIZED_SIZE
    };

  public:

    // ----------------------------------------------------------------------
    // Types
    // ----------------------------------------------------------------------

    //! The port callback function type
    typedef void (*CompFuncPtr)(
      Fw::PassiveComponentBase* callComp,
      FwIndexType portNum,
      const T& t,
      T& tRef
    );

  public:

    // ----------------------------------------------------------------------
    // Input Port Member functions
    // ----------------------------------------------------------------------

    //! Constructor
    InputAbsTypePort();

    //! Initialization function
    void init();

    //! Register a component
    void addCallComp(
        Fw::PassiveComponentBase* callComp, //!< The containing component
        CompFuncPtr funcPtr //!< The port callback function
    );

    //! Invoke a port interface
    void invoke(
        const T& t,
        T& tRef
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

//! Output AbsType port
//! A port with abstract type parameters
class OutputAbsTypePort :
  public Fw::OutputPortBase
{

  public:

    // ----------------------------------------------------------------------
    // Output Port Member functions
    // ----------------------------------------------------------------------

    //! Constructor
    OutputAbsTypePort();

    //! Initialization function
    void init();

    //! Register an input port
    void addCallPort(
        InputAbsTypePort* callPort //!< The input port
    );

    //! Invoke a port interface
    void invoke(
        const T& t,
        T& tRef
    ) const;

  private:

    // ----------------------------------------------------------------------
    // Member variables
    // ----------------------------------------------------------------------

    //! The pointer to the input port
    InputAbsTypePort* m_port;

};

#endif
