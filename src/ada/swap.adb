procedure Swap with SPARK_Mode => On is
   function Foo return Integer with Import;
   function Bar return Integer with Import;

   X : Integer := Foo;
   Y : Integer := Bar;
begin
   declare
      Tmp : Integer;
   begin
      Tmp := X;
      X := Y;
      Y := Tmp;
   end;
end Swap;
