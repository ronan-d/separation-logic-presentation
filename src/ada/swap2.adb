pragma Assertion_Policy (Check);

procedure Swap2 with SPARK_Mode => On is
   function Foo return Integer with Import;
   function Bar return Integer with Import;

   X : Integer := Foo;
   Y : Integer := Bar;

   X0 : constant Integer := X with Ghost;
   Y0 : constant Integer := Y with Ghost;
begin
   declare
      Tmp : Integer;
   begin
      Tmp := X;
      X := Y;
      Y := Tmp;
   end;

   pragma Assert (X = Y0);
   pragma Assert (Y = X0);
end Swap2;
