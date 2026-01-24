

import LeanGrow.Src.Utils.Std.ByteArray


#check 1


#check Array.insertIdx!

#eval Array.insertIdx! #[1,2,3] 0 42

#eval Array.insertIdx! #[1,2,3] 2 42

#eval Array.insertIdx! #[1,2,3] 3 42

#check ByteArray.drop
#check ByteArray.take

#eval ByteArray.drop ⟨#[1,2,3]⟩ 0
#eval ByteArray.take ⟨#[1,2,3]⟩ 0

#eval ByteArray.drop ⟨#[1,2,3]⟩ 1
#eval ByteArray.take ⟨#[1,2,3]⟩ 1

#eval ByteArray.drop ⟨#[1,2,3]⟩ 2
#eval ByteArray.take ⟨#[1,2,3]⟩ 2

#eval ByteArray.drop ⟨#[1,2,3]⟩ 3
#eval ByteArray.take ⟨#[1,2,3]⟩ 3

#eval ByteArray.drop ⟨#[1,2,3]⟩ 4
#eval ByteArray.take ⟨#[1,2,3]⟩ 4


#eval "LLE".toUTF8.data
