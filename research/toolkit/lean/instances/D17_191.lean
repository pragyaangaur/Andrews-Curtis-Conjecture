import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 191 of the cap-17 certificate: slots 97792 .. 98303 -/
theorem chk_191 : chunkCheck 17 T stdSt 97792 512 = true := by decide +kernel

end Row17
