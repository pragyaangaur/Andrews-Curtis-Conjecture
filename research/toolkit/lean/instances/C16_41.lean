import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 41 of the cap-16 certificate: slots 41984 .. 43007 -/
theorem chk_41 : chunkCheck 16 T stdSt 41984 1024 = true := by decide +kernel

end Row16
