// ======================================================================
// \title  EmptyComponentAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for Empty component base class
// ======================================================================

#include <cstdio>

#include "Fw/Types/Assert.hpp"
#if FW_ENABLE_TEXT_LOGGING
#include "Fw/Types/String.hpp"
#endif
#include "base/EmptyComponentAc.hpp"

namespace {
  // Get the max size by constructing a union of the async input, command, and
  // internal port serialization sizes
  union BuffUnion {
    // No async input ports
  };

  // Define a message buffer class large enough to handle all the
  // asynchronous inputs to the component
  class ComponentIpcSerializableBuffer :
    public Fw::SerializeBufferBase
  {

    public:

      enum {
        // Max. message size = size of data + message id + port
        SERIALIZATION_SIZE =
          sizeof(BuffUnion) +
          sizeof(NATIVE_INT_TYPE) +
          sizeof(NATIVE_INT_TYPE)
      };

      NATIVE_UINT_TYPE getBuffCapacity() const {
        return sizeof(m_buff);
      }

      U8* getBuffAddr() {
        return m_buff;
      }

      const U8* getBuffAddr() const {
        return m_buff;
      }

    private:
      // Should be the max of all the input ports serialized sizes...
      U8 m_buff[SERIALIZATION_SIZE];

  };
}

// ----------------------------------------------------------------------
// Component initialization
// ----------------------------------------------------------------------

void EmptyComponentBase ::
  init(NATIVE_INT_TYPE instance)
{
  // Initialize base class
  Fw::PassiveComponentBase::init(instance);
}

// ----------------------------------------------------------------------
// Component construction and destruction
// ----------------------------------------------------------------------

EmptyComponentBase ::
  EmptyComponentBase(const char* compName) :
    Fw::PassiveComponentBase(compName)
{

}

EmptyComponentBase ::
  ~EmptyComponentBase()
{

}
