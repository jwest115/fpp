// ======================================================================
// \title  ExplicitEnumAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for Explicit enum
// ======================================================================

#ifndef M_ExplicitEnumAc_HPP
#define M_ExplicitEnumAc_HPP

#include "FpConfig.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

namespace M {

  //! An enum with explicit constant values
  class Explicit :
    public Fw::Serializable
  {

    public:

      // ----------------------------------------------------------------------
      // Types
      // ----------------------------------------------------------------------

      //! The serial representation type
      typedef U8 SerialType;

      //! The raw enum type
      enum T {
        //! Member X
        X = 1,
        Y = 2,
      };

      //! For backwards compatibility
      typedef T t;

    public:

      // ----------------------------------------------------------------------
      // Constants
      // ----------------------------------------------------------------------

      enum {
        //! The size of the serial representation
        SERIALIZED_SIZE = sizeof(SerialType),
        //! The number of enumerated constants
        NUM_CONSTANTS = 2,
      };

    public:

      // ----------------------------------------------------------------------
      // Constructors
      // ----------------------------------------------------------------------

      //! Constructor (default value of X)
      Explicit()
      {
        this->e = X;
      }

      //! Constructor (user-provided value)
      Explicit(
          const T e //!< The raw enum value
      )
      {
        this->e = e;
      }

      //! Copy constructor
      Explicit(
          const Explicit& obj //!< The source object
      )
      {
        this->e = obj.e;
      }

    public:

      // ----------------------------------------------------------------------
      // Operators
      // ----------------------------------------------------------------------

      //! Copy assignment operator (object)
      Explicit& operator=(
          const Explicit& obj //!< The source object
      );

      //! Copy assignment operator (raw enum)
      Explicit& operator=(
          T e //!< The enum value
      );

      //! Conversion operator
      operator T() const
      {
        return this->e;
      }

      //! Equality operator
      bool operator==(T e) const
      {
        return this->e == e;
      }

      //! Inequality operator
      bool operator!=(T e) const
      {
        return !(*this == e);
      }

#ifdef BUILD_UT

      //! Ostream operator
      friend std::ostream& operator<<(
          std::ostream& os, //!< The ostream
          const Explicit& obj //!< The object
      );

#endif

    public:

      // ----------------------------------------------------------------------
      // Member functions
      // ----------------------------------------------------------------------

      //! Check raw enum value for validity
      bool isValid() const;

      //! Serialize raw enum value to SerialType
      Fw::SerializeStatus serialize(
          Fw::SerializeBufferBase& buffer //!< The serial buffer
      ) const;

      //! Deserialize raw enum value from SerialType
      Fw::SerializeStatus deserialize(
          Fw::SerializeBufferBase& buffer //!< The serial buffer
      );

#if FW_SERIALIZABLE_TO_STRING || BUILD_UT

      //! Convert enum to string
      void toString(
          Fw::StringBase& sb //!< The StringBase object to hold the result
      ) const;

#endif

    public:

      // ----------------------------------------------------------------------
      // Member variables
      // ----------------------------------------------------------------------

      //! The raw enum value
      T e;

  };

}

#endif