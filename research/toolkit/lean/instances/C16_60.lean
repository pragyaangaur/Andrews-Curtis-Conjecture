import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 60 of the cap-16 certificate: slots 61440 .. 62463 -/
theorem chk_60 : chunkCheck 16 T stdSt 61440 1024 = true := by decide +kernel

end Row16
