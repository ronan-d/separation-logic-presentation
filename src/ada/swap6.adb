pragma Assertion_Policy (Check);

procedure Swap6 with SPARK_Mode => On is
   type Modular_Integer is mod 256;

   function Foo return access Modular_Integer with Import;
   function Bar return access Modular_Integer with Import;

   -- Not valid SPARK!
   X : constant access Modular_Integer := Foo;
   Y : constant access Modular_Integer := Bar;

   X0 : constant Modular_Integer := X.all with Ghost;
   Y0 : constant Modular_Integer := Y.all with Ghost;
begin
   X.all := X.all xor Y.all;
   Y.all := Y.all xor X.all;
   X.all := X.all xor Y.all;

   pragma Assert (X.all = Y0 and Y.all = X0);
end Swap6;
