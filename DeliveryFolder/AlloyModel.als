// + - - - - - - - - - - - - - - - - - - - +
// |             SIGNATURE                 |
// + - - - - - - - - - - - - - - - - - - - +

// Booleans
abstract sig Boolean {}
lone sig True extends Boolean {}
lone sig False extends Boolean {}


one sig SandC {
	var universities: some University,
	var companies: some Company,
	var students: some Student
}
enum Status {
	OPEN,
	ONGOING,
	CLOSED
}
enum ApplicationResults {
	PENDING,
	APPROVED,
	REJECTED
}
// Date time , represented as an integer
sig DateTime {
    time : one Int
}{
time >= 0
}
sig Email {}{
    one this .~ username
}
sig Password {}{
    some this .~ password
}
var sig CV{}{
	one s: Student| this=s.cv
}
sig Internship {
    state: one Status,
    startDate: one Int,
    endDate: one Int,
    applicationDeadline: one Int,
    company: one Company // Direct relationship with the company
} {
    startDate < endDate
    applicationDeadline < startDate
}
sig InternshipApplication {
    application: one Internship,
    result: one ApplicationResults,
    submissionDate: one Int
} {
    submissionDate >= 0
}
sig SupportRequest {
	student: one Student,
	company: one Company,
	university: one University,
	internship: one Internship,
	state: one Status
}
sig Feedback {
	text: String
}
//Users
abstract sig User {
username : disj one Email,
password : one Password,
feedback: set Feedback
}
sig Company extends User {
	internshipOffer: some Internship
}
sig University extends User{}
sig Student extends User {
	var cv: disj lone CV,
	var interApp: set InternshipApplication,
	ongoingIntern: lone Internship, // "lone" to allow no ongoing internships
	university: one University
}

// + - - - - - - - - - - - - - - - - - - - +
// |                FACT                   |
// + - - - - - - - - - - - - - - - - - - - +
fact InternshipOfferedByOneCompany {
   // Each Internship is offered by only one company
   always(all disj c1, c2: Company | c1.internshipOffer != none and  c2.internshipOffer != none implies
    (c1.internshipOffer & c2.internshipOffer) = none)
}
fact InternshipWithOneStudent{
   // Each Internship is done by one student
   always(all disj s1, s2: Student| s1.ongoingIntern!= none and  s2.ongoingIntern != none implies
    (s1.ongoingIntern & s2.ongoingIntern) = none)
}
fact UniqueRelationships {
   // Ensures unique CV per student
    always(all s: Student | lone s.cv)
}
fact StudentMustHaveUniversity {
    // Each student must have exactly one university
    always(all s: Student | one s.university)
}
fact StudentUniversityAssociation {
    // Ensures student and university association consistency
    always(all s: Student | one s.university)
}
fact InternshipStudentCompanyConsistency {
    // Links internships to students and their companies
    always(all s: Student |
        some s.ongoingIntern implies s.ongoingIntern.company in Company)
} 
fact CVExistenceCondition {
    // Ensures CVs belong to students
    always(all c: CV | some s: Student | c in s.cv)
}
fact StudentMustHaveCVForInternship {
    // Students need a CV for internships
    always(all s: Student | 
        (some s.ongoingIntern or some s.interApp) implies some s.cv)
}
fact ApplicationExistenceCondition {
    // Ensures applications belong to internships and students
    always(all a: InternshipApplication | 
        some s: Student | (a in s.interApp and a.application in Internship))
}
fact ApplicationLinkedToInternship {
    // Applications must link to one internship
    always(all app: InternshipApplication | one app.application)
}
fact OngoingInternshipStatus {
    // Validates internship state and student participation
    always(all i: Internship | i.state = ONGOING iff some i.~ongoingIntern)
}
fact FeedbackLinkedToUser {
    // Feedback must be linked to a user
    always(all f: Feedback | some f.~feedback)
}
fact SupportRequestConsistency {
    // Validates support request structure
    always(all req: SupportRequest | 
        req.student.ongoingIntern = req.internship and
        req.company = req.internship.company)
}
fact UniqueApplicationPerStudent {
    // One application per internship per student
   always( all s: Student, i: Internship | 
        #(s.interApp & i.~application) <= 1)
}
fact ApplicationSubmissionDateCondition {
    // Applications must be submitted before deadlines
    always(all a: InternshipApplication |
        a.submissionDate < a.application.applicationDeadline)
}
fact InternshipOngoingCondition {
    // Ongoing internships must respect date constraints
    always(all i: Internship | 
        (i.state = ONGOING) iff (i.startDate <= i.endDate))
}
fact RejectApplicationsOnInternshipStart {
    // Reject pending applications when internship starts
    always(all i: Internship | 
        i.state = ONGOING implies 
        all a: InternshipApplication | 
            (a.application = i and a.result != APPROVED) => 
            a.result = REJECTED)
}
fact SupportRequestTerminationCondition {
    // Support requests end when internships close
    always(all req: SupportRequest |
        req.internship.state = CLOSED implies req.state = CLOSED)
}
fact NoOverlapBetweenInternshipStates {
    // Validates mutual exclusivity of internship states
    always(no i: Internship | 
        (i.state = OPEN and (i.state = ONGOING or i.state = CLOSED)) or
        (i.state = ONGOING and (i.state = OPEN or i.state = CLOSED)) or
        (i.state = CLOSED and (i.state = OPEN or i.state = ONGOING)))
}
fact SingleSupportRequestPerInternship {
    // Only one support request per internship
    always(all i: Internship | #(i.~internship) <= 1)
}
fact noStudentContractUniveristy{
	always(not some s: Student| s in SandC.students and s.university not in SandC.universities)
}
fact{
	always(all s: Student| s not in SandC.students implies not s.interApp.application.~internshipOffer in SandC.companies)
}



// + - - - - - - - - - - - - - - - - - - - +
// |             PREDICATES                |
// + - - - - - - - - - - - - - - - - - - - +

pred EligibleForInternship(s: Student, i: Internship) {
    // Checks if a student is eligible for an internship
    some s.cv
    i.state = OPEN
    no i.~ongoingIntern
}
pred ValidSupportRequest(req: SupportRequest) {
    // Validates a support request
    req.internship.state = ONGOING
    req.student.ongoingIntern = req.internship
    req.student.university = req.university
}
pred ApplicationCompleted(app: InternshipApplication) {
    // Checks if an application is evaluated
    app.result != PENDING
}
pred UniqueCredentials() {
    // Ensures unique username and password for all users
    all disj u1, u2: User | u1.username != u2.username and u1.password != u2.password
}
pred HasCompletedInternship(s: Student) {
    // Checks if a student completed an internship
    some i: s.ongoingIntern | i.state = CLOSED
}
pred IsValidApplication(a: InternshipApplication) {
    // Verifies an application is valid
    a.result = PENDING and
    a.application.state = OPEN
}
pred CheckStudentInternships(s: Student) {
    // Ensures internships of a student have valid states
    all i: s.ongoingIntern |
        i.state in Status - OPEN
}
pred ValidateInternshipDates(i: Internship) {
    // Validates that internship dates are consistent
    i.startDate < i.endDate
}
// + - - - - - - - - - - - - - - - - - - - +
// |        TEMPORAL PREDICATES            |
// + - - - - - - - - - - - - - - - - - - - +

pred StudentSubscribers[s: Student]{
	//pre-condition
	s not in SandC.students
	s.university in SandC.universities
	//post-condition
	always(s in SandC.students' and
	SandC.students'=SandC.students+s)
}
pred CompanySubscribers[c: Company]{
	//pre-condition
	c not in SandC.companies
	//post-condition
	always(c in SandC.companies' and
	SandC.companies'=SandC.companies+c)
}
pred UniveristyContract[u: University]{
	//pre-condition
	u not in SandC.universities
	//post-condition
	always(u in SandC.universities' and
	SandC.universities'=SandC.universities+u)
	//postpost-condition (only for fun)
	some s: Student| (s.university'=u and s not in SandC.students' 
	and s.ongoingIntern'=none and s.interApp'=none and always(
	s in SandC.students'' and
	SandC.students''=SandC.students+s))
}
pred LoadCV[s: Student, cvs: CV]{
	//pre-condition
	s in SandC.students
	s.university in SandC.universities 
	s.interApp=none 
	s.cv =none
	cvs.~cv=none
	//post-condition
	all s1: Student-s| s1.cv=s1.cv'
	s.cv'=cvs and cvs.~cv'=s
	s in SandC.students'
	s.university in SandC.universities'
	 SandC.students'= SandC.students
}
pred InterApp[s: Student, ia: InternshipApplication]{
	//pre-condition
	s.interApp!=none and not ia in s.interApp
	s in SandC.students
	//post-condition
	all s1: Student-s| s1.interApp=s1.interApp'
	   ia in s.interApp'
	       s.interApp'=s.interApp+ia
}

// + - - - - - - - - - - - - - - - - - - - +
// |               ASSERTION               |
// + - - - - - - - - - - - - - - - - - - - +

assert EachStudentHasUniversity {
    // Each student must be associated with exactly one university
    all s: Student | one s.university
}
assert ValidInternshipState {
    // Ensures all internships have valid states
    all i: Internship | i.state in Status
}
assert AllApplicationsEvaluated {
    // Verifies that all applications have been evaluated
    all app: InternshipApplication | ApplicationCompleted[app]
}
assert ApplicationsToOpenInternships {
    // Ensures applications are only made to open internships
    all a: InternshipApplication |
        a.application.state = OPEN
}
assert NoOverlapBetweenOpenAndOngoing {
    // Checks there is no overlap between OPEN and ONGOING internships
    no i: Internship | i.state = OPEN and i.state = ONGOING
}
assert ValidSupportRequest {
    // Validates that all support requests refer to valid internships
    all sr: SupportRequest | sr.internship in Internship
}
assert FeedbackHasUser {
    // Ensures every feedback is linked to a user
    all f: Feedback | some u: User | f in u.feedback
}
assert InternshipOngoingValidity {
    // Validates that ONGOING internships have consistent dates
    all i: Internship |
        i.state = ONGOING implies i.startDate < i.endDate
}

// + - - - - - - - - - - - - - - - - - - - +
// |                 RUN                   |
// + - - - - - - - - - - - - - - - - - - - +

run {
   some s: Student, c: Company | 
      s in SandC.students and c in SandC.companies
}
