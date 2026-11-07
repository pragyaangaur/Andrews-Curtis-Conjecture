import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 58 of the cap-16 certificate: slots 59392 .. 60415 -/
theorem chk_58 : chunkCheck 16 T stdSt 59392 1024 = true := by decide +kernel

end Row16
