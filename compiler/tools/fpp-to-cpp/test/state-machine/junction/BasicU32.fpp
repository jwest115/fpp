module FppTest {

  module SmJunction {

    @ A basic state machine with a U32 junction
    state machine BasicU32 {

      @ Action a
      action a: U32

      @ Action b
      action b

      @ Signal s
      signal s: U32

      @ Guard g
      guard g: U32

      @ Initial transition
      initial enter S1

      @ State S1
      state S1 {

        @ State transition
        on s enter J

      }

      @ Junction J
      junction J {
        if g do { a } enter S2 else do { b } enter S3
      }

      @ State S2
      state S2

      @ State S3
      state S3

    }

  }

}