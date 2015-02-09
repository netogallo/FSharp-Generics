 namespace TheNameSpace {
    using System.Reflection;
    using System;
    using Generics;

    public class TheProvidedType{

        private void ThePicker(Rep.Meta constr){

            

            if(){


            }


            foreach(var m in this.GetType().GetMethods(BindingFlags.FlattenHierarchy | BindingFlags.Instance | BindingFlags.Public)){
                        Console.WriteLine(m.Name);
            }
        }
    }
 }
