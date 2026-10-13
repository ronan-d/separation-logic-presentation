pragma Assertion_Policy (Check);

procedure Swap4 with SPARK_Mode => On is
   type Modular_Integer is mod 256;

   function Foo return Integer with Import;
   function Bar return Integer with Import;

   X : Integer := Foo;
   Y : Integer := Bar;

   X0 : constant Integer := X with Ghost;
   Y0 : constant Integer := Y with Ghost;
begin
   X := X xor Y;
   Y := Y xor X;
   X := X xor Y;

   pragma Assert (X = Y0);
   pragma Assert (Y = X0);
end Swap4;
