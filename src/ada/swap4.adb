pragma Assertion_Policy (Check);

procedure Swap4 with SPARK_Mode => On is
   type Modular_Integer is mod 256;

   function Foo return Modular_Integer with Import;
   function Bar return Modular_Integer with Import;

   X : Modular_Integer := Foo;
   Y : Modular_Integer := Bar;

   X0 : constant Modular_Integer := X with Ghost;
   Y0 : constant Modular_Integer := Y with Ghost;
begin
   X := X xor Y;
   Y := Y xor X;
   X := X xor Y;

   pragma Assert (X = Y0 and Y = X0);
end Swap4;
