---
title: Assignments
layout: default
start: 14 Sep 2015, 00:00 (Europe/Zurich)
index: 3
---

### Administrivia

Over the course of the semester, we will post six assignments that will require you to code up six moderately complex Scala applications (one per each assignment) that highlight certain theoretical aspects of the course. **Update (2 Dec 2015):** we have cancelled project #6 in favor of additional pen & paper sessions.

Every assignment will become available on this website at due time (usually after the deadline of the previous assignment). We will be notifying you about the arrival of new assignments on the [mailing list](/mailing-list.html), so be sure to join it.

We encourage you to team up when working on assignments. Teams can consist of one, two or three students and should not intersect with each other. It is okay to share ideas between teams, but sharing code is prohibited.

### Getting started with Scala

All development during the course will be done in Scala. Here we provide the instructions
how to setup the Eclipse-based Scala IDE:

Before you can import project into Eclipse you need to generate an eclipse project using
[the sbt build tool](http://www.scala-sbt.org/download.html):

1. Open command-line terminal.
1. Download and unpack the assignment skeleton zip from the project description page.
1. Navigate to the folder where you unpacked the assignment skeleton.
1. Run `sbt eclipse` to generate IDE project definition. This might take a while.

After completing that you can import the project into the IDE:

1. Download Eclipse with built-in Scala plugin from [http://scala-ide.org/download/sdk.html](http://scala-ide.org/download/sdk.html).
1. Unpack and launch the downloaded application.
1. Go to `File > Import > Existing Project into Workspace`.
1. Select the directory where you unpacked the assignment.
1. Click `Finish`.
1. You should be all set.

If you don't like Eclipse, feel free to use alternative editors or even develop in console,
as long as your project passes our tests.

### Submitting your solutions

1. Zip your project directory, making sure that you haven't created or removed any files from the provided template for the corresponding project. For instance, if the template contained files Arithmetic.scala and Terms.scala in /src/main/scala/fos, don't move these files around or create additional helper files.

1. Send the archive produced during the previous step to the email address specified in the welcome message of the mailing list.
  * The subject of the email should be "Project X (YYYYYY, ZZZZZZ, ...)", where X is the number of the project, and YYYYYY/ZZZZZZ/... are SCIPER numbers of the authors.
  * The body of the email doesn't matter, because our grading bot can't read.
  * Don't forget the attachment.

1. Wait for a response from the grading bot. The response will either contain a rejection notice along with the detailed error message or an acceptance notice with the results of running your submission against our test suite.

1. If you don't receive a response from the bot, or you get your submission rejected without a good reason, contact the staff.


1. If you're not content with your results, follow the instructions in the reply email to try and improve your score. You can retry the submission as many times as you want before the deadline hits, and that won't result in any penalties to your final score.

### Late submissions

If you miss a deadline, you can still submit your project, however your grade will be reduced. Late submissions will be graded with 30% deduction of points for every day after the deadline.