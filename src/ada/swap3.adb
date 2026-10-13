pragma Assertion_Policy (Check);

procedure Swap3 with SPARK_Mode => On is
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
      pragma Assert (Y = Y0 and X = X0);
   
      Tmp := X;

      pragma Assert (Y = Y0 and Tmp = X0);

      X := Y;

      pragma Assert (X = Y0 and Tmp = X0);

      Y := Tmp;
   end;

   pragma Assert (X = Y0 and Y = X0);
end Swap3;
