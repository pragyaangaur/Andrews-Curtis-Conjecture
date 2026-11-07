import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 163 of the cap-16 certificate: slots 166912 .. 167935 -/
theorem chk_163 : chunkCheck 16 T stdSt 166912 1024 = true := by decide +kernel

end Row16
