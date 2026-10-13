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
   pragma Assert (Y = Y0);
   pragma Assert (X = X0);
   pragma Assert ((Y xor X xor Y) = X0);

   X := X xor Y;

   pragma Assert (Y = Y0);
   pragma Assert ((X xor Y xor X) = Y0);
   pragma Assert ((Y xor X) = X0);

   Y := Y xor X;

   pragma Assert ((X xor Y) = Y0);
   pragma Assert (Y = X0);

   X := X xor Y;

   pragma Assert (X = Y0);
   pragma Assert (Y = X0);
end Swap4;
