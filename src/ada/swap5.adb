pragma Assertion_Policy (Check);

procedure Swap5 with SPARK_Mode => On is
   type Modular_Integer is mod 256;

   function Foo return Modular_Integer with Import;
   function Bar return Modular_Integer with Import;

   X : Modular_Integer := Foo;
   Y : Modular_Integer := Bar;

   X0 : constant Modular_Integer := X with Ghost;
   Y0 : constant Modular_Integer := Y with Ghost;
begin
   pragma Assert (X = X0 and Y = Y0);

   X := X xor Y;

   pragma Assert (X = (X0 xor Y0) and Y = Y0);

   Y := Y xor X;

   pragma Assert (X = (X0 xor Y0) and Y = (Y0 xor X0 xor Y0));
   pragma Assert (X = (X0 xor Y0) and Y = X0);

   X := X xor Y;

   pragma Assert (X = (X0 xor Y0 xor X0) and Y = X0);
   pragma Assert (X = Y0 and Y = X0);
end Swap5;
