// ======================================================================
// \title  Modules1SerializableAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for Modules1 struct
// ======================================================================

#ifndef M_Modules1SerializableAc_HPP
#define M_Modules1SerializableAc_HPP

#include "FpConfig.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

namespace M {

  class Modules1 :
    public Fw::Serializable
  {

    public:

      // ----------------------------------------------------------------------
      // Constants
      // ----------------------------------------------------------------------

      enum {
        //! The size of the serial representation
        SERIALIZED_SIZE =
          sizeof(U32) +
          sizeof(F32)
      };

    public:

      // ----------------------------------------------------------------------
      // Constructors
      // ----------------------------------------------------------------------

      //! Constructor (default value)
      Modules1();

      //! Member constructor
      Modules1(
          U32 x,
          F32 y
      );

      //! Copy constructor
      Modules1(
          const Modules1& obj //!< The source object
      );

    public:

      // ----------------------------------------------------------------------
      // Operators
      // ----------------------------------------------------------------------

      //! Copy assignment operator
      Modules1& operator=(
          const Modules1& obj //!< The source object
      );

      //! Equality operator
      bool operator==(
          const Modules1& obj //!< The other object
      ) const;

      //! Inequality operator
      bool operator!=(
          const Modules1& obj //!< The other object
      ) const;

#ifdef BUILD_UT

      //! Ostream operator
      friend std::ostream& operator<<(
          std::ostream& os, //!< The ostream
          const Modules1& obj //!< The object
      );

#endif

    public:

      // ----------------------------------------------------------------------
      // Member functions
      // ----------------------------------------------------------------------

      //! Serialization
      Fw::SerializeStatus serialize(
          Fw::SerializeBufferBase& buffer //!< The serial buffer
      ) const;

      //! Deserialization
      Fw::SerializeStatus deserialize(
          Fw::SerializeBufferBase& buffer //!< The serial buffer
      );

#if FW_SERIALIZABLE_TO_STRING

      //! Convert struct to string
      void toString(
          Fw::StringBase& sb //!< The StringBase object to hold the result
      ) const;

#endif

      // ----------------------------------------------------------------------
      // Getter functions
      // ----------------------------------------------------------------------

      //! Get member x
      U32 getx() const
      {
        return this->m_x;
      }

      //! Get member y
      F32 gety() const
      {
        return this->m_y;
      }

      // ----------------------------------------------------------------------
      // Setter functions
      // ----------------------------------------------------------------------

      //! Set all members
      void set(
          U32 x,
          F32 y
      );

      //! Set member x
      void setx(U32 x);

      //! Set member y
      void sety(F32 y);

    protected:

      // ----------------------------------------------------------------------
      // Member variables
      // ----------------------------------------------------------------------

      U32 m_x;
      F32 m_y;

  };

}

#endif
