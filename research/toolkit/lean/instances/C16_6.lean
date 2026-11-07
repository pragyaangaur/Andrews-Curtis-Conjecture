import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 6 of the cap-16 certificate: slots 6144 .. 7167 -/
theorem chk_6 : chunkCheck 16 T stdSt 6144 1024 = true := by decide +kernel

end Row16
