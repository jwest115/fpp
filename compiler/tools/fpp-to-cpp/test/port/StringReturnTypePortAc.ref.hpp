// ======================================================================
// \title  StringReturnTypePortAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for StringReturnType port
// ======================================================================

#ifndef M_StringReturnTypePortAc_HPP
#define M_StringReturnTypePortAc_HPP

#include <cstdio>
#include <cstring>
#include <Fw/FPrimeBasicTypes.hpp>

#include "Fw/Comp/PassiveComponentBase.hpp"
#include "Fw/Port/InputPortBase.hpp"
#include "Fw/Port/OutputPortBase.hpp"
#include "Fw/Types/String.hpp"

namespace M {

  //! Input StringReturnType port
  //! A port with a string return type
  class InputStringReturnTypePort :
    public Fw::InputPortBase
  {

    public:

      // ----------------------------------------------------------------------
      // Constants
      // ----------------------------------------------------------------------

      enum {
        //! The size of the serial representations of the port arguments
        SERIALIZED_SIZE = 0
      };

    public:

      // ----------------------------------------------------------------------
      // Types
      // ----------------------------------------------------------------------

      //! The port callback function type
      typedef Fw::String (*CompFuncPtr)(
        Fw::PassiveComponentBase* callComp,
        FwIndexType portNum
      );

    public:

      // ----------------------------------------------------------------------
      // Input Port Member functions
      // ----------------------------------------------------------------------

      //! Constructor
      InputStringReturnTypePort();

      //! Initialization function
      void init();

      //! Register a component
      void addCallComp(
          Fw::PassiveComponentBase* callComp, //!< The containing component
          CompFuncPtr funcPtr //!< The port callback function
      );

      //! Invoke a port interface
      Fw::String invoke();

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

  //! Output StringReturnType port
  //! A port with a string return type
  class OutputStringReturnTypePort :
    public Fw::OutputPortBase
  {

    public:

      // ----------------------------------------------------------------------
      // Output Port Member functions
      // ----------------------------------------------------------------------

      //! Constructor
      OutputStringReturnTypePort();

      //! Initialization function
      void init();

      //! Register an input port
      void addCallPort(
          InputStringReturnTypePort* callPort //!< The input port
      );

      //! Invoke a port interface
      Fw::String invoke() const;

    private:

      // ----------------------------------------------------------------------
      // Member variables
      // ----------------------------------------------------------------------

      //! The pointer to the input port
      InputStringReturnTypePort* m_port;

  };

}

#endif
