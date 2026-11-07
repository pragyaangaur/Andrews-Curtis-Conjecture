import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 78 of the cap-17 certificate: slots 39936 .. 40447 -/
theorem chk_78 : chunkCheck 17 T stdSt 39936 512 = true := by decide +kernel

end Row17
